
#ifndef CALC_CLAUSESET_
#define CALC_CLAUSESET_

#include <list>
#include <iostream>

#include "logic/term.h"

namespace calc
{
   struct clauseset
   {
      std::list< logic::term > conj;

      clauseset( ) noexcept = default;

      bool subsumes( const logic::term& disj ) const;
         // True if disj is subsumed by cls. 
      void remove_subsumed( const logic::term& disj );
         // Remove disjunctions subsumed by disj. 
      void insert( const logic::term& disj );
         // Always inserts.

      logic::term pick( );
         // Pick (shortest) clause and remove it from conj.

      size_t size( ) const { return conj. size( ); } 
     
      void print( std::ostream& out ) const; 

   };

   // I believe that all of this belongs in another file.
   // Probably one should remove formulaset.

   bool 
   contains( const logic::term& lit, const logic::term& form, size_t skip );
      // Works for kleene_and and for kleene_or. 

   bool subset( const logic::term& form1, size_t skip1,
                const logic::term& form2, size_t skip2 );
      // True if form1 \ skip1 is a subset of form2 \ skip2.
      // We use 'subset' instead of 'subsumes', so that it
      // can be also applied on conjunctions.

   inline bool subset( const logic::term& form1, const logic::term& form2 )
   {
      return subset( form1, form1. view_kleene( ). size( ),
                     form2, form2. view_kleene( ). size( ));
   }

   // Repeats are removed:

   logic::term
   merge( const logic::term& form1, size_t skip1,
          const logic::term& form2, size_t skip2 );

}

#endif

