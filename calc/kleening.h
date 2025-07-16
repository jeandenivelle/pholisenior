
#ifndef CALC_CLAUSIFY_
#define CALC_CLAUSIFY_

#include <vector>

#include "polarity.h"

#include "logic/term.h"
#include "logic/context.h"

namespace calc
{
   logic::selector kleenop( logic::selector op );
      // Get the kleening of op, for a monotone operator.

   logic::term apply( const logic::term& f, polarity pol );
      // If pol is positive, we return f.
      // If pol is negative, we return either not(f),
      // or try to remove a negation from f.

   logic::term apply_prop( const logic::term& f, polarity pol ); 
      // Return prop(f) or not( prop(f)).

   logic::term kleene_top( const logic::term& f, polarity pol );
   logic::term kleene_top_prop( const logic::term& f, polarity pol ); 
      // Make sure that f is a literal, or
      // the top operator of f is a Kleene operator.
 
   logic::term flatten_conj( logic::term f, unsigned int level ); 
   void flatten( logic::context& ctxt, const logic::term& f,
                 std::vector< logic::term > & into, unsigned int level );
}

#endif

