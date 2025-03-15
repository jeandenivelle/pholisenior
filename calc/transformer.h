
#ifndef CALC_TRANSFORMER_
#define CALC_TRANSFORMER_

#include <vector>
#include <algorithm>

#include "logic/term.h"
#include "logic/beliefstate.h"
#include "logic/context.h"

#include "namegenerator.h"
#include "polarity.h"

namespace calc
{

   // We need explicit values, because we put them in a priority
   // queue, where the highest (most unfinished) step is 
   // always processed first.

   enum transstep 
   {
      step_cls = 1,
      step_anf = 2,
      step_kleening = 3,
      step_splitequiv = 4,
      step_rmlet = 5, 
      step_none = 6
   };

   const char* getcstring( transstep step );

   inline std::ostream& operator << ( std::ostream& out, transstep step )
      { out << getcstring( step ); return out; }

   struct subformula
   {
      logic::exact pred;
         // If you need the types of the arguments,
         // you can look in the beliefstate.
         // The arguments are De Bruijn variables, applied
         // from high (far) to low (0).

      logic::term form;
         // The free De Bruijn variables of form are always 
         // in [ 0 .. types. size( ) ). 

      polarity pol; 
         // Applies only to the predicate.

      transstep last;
         // Last step that was applied.

      size_t nr; 
      
      subformula( logic::exact pred, logic::term&& form,
                  polarity pol, transstep last, size_t nr )
         : pred( pred ),
           form( std::move( form )),
           pol( pol ),
           last( last ),
           nr( nr ) 
      { }

      subformula( ) = delete;
      subformula( subformula&& ) noexcept = default;
      subformula& operator = ( subformula&& ) noexcept = default;
         // Blocking copy.

      void print( std::ostream& out ) const;
   };

   bool operator < ( const subformula& sub1, const subformula& sub2 );

   struct transformer 
   {
      namegenerator gen;

      std::vector< subformula > forms;   
         // std::priority gives to many problems.
         // 1. It cannot be printed.
         // 2. There is no operation that moves out (and pop) the top.
         //    I now use std::push_heap( ) and std::pop_heap( ).

      size_t nr = 0;

      transformer( ) noexcept = default;
      transformer( transformer&& ) noexcept = default;
      transformer& operator = ( transformer&& ) noexcept = default;


      void push( logic::exact pred, 
                 logic::term form, polarity pol, transstep last );

      subformula extract_top( );
         // This function is move only. It is missing in 
         // std::priority_queue. Because of this, we use
         // std::vector, and push/pop_heap instead.
 
      identifier
      fresh_ident( const logic::beliefstate& blfs,
                   const char* namebase );


      void add_initial( logic::beliefstate& blfs, logic::term init );
         // If you want to negate conj, you have to do it by 
         // yourself. 
         // We need a copy, because we will move it into unchecked.
         // It's called 'add' because we hide that we use a 
         // priority queue.

      void flush( logic::beliefstate& blfs );

      std::pair< logic::term, logic::term > 
      extractsubform( logic::beliefstate& blfs,
                      const char* namebase, 
                      const logic::context& ctxt, 
                      logic::term ff );

         // split a formula by introducing a definition for it.
         // We return the atom that should be put in place of the formula, 
         // and the formula, with its variables normalized to
         // #(n-1), ... #1, #0. 

      void print( std::ostream& out ) const; 
   };

   logic::context
   get_context( logic::exact pred, const logic::beliefstate& blfs );

   logic::term atom( identifier pred, const logic::type& predtype );
   logic::term forall( const logic::type& predtype, logic::term form );

   logic::term
   clausify( logic::beliefstate& blfs, namegenerator& gen,
             logic::context& ctxt, logic::term& f, unsigned int alt );
      // Term f must have Kleene operations only, and in NNF.
      // Even level means and/forall.
      // Odd level means or/exists.
}

#endif

