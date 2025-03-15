
#ifndef CALC_ALTERNATING_
#define CALC_ALTERNATING_

#include "transformer.h"

namespace calc
{
   bool isliteral( const logic::term& f );

   // Formula f must be in KNF:

   // Result will be a disjunction of exists of alt_foralls( ).

   logic::term alt_disj( logic::term f );
      // We always create a disjunction, but we do not create
      // empty quantifiers.

   void 
   flatten_disj( logic::context& ctxt, const logic::term& f,
                 std::vector< logic::term > & into );

   logic::term alt_conj( logic::term f );
      // We always create a conjunction, but we do not create 
      // empty quantifiers.

   void 
   flatten_conj( logic::context& ctxt, const logic::term& f,
                 std::vector< logic::term > & into );
}

#endif

