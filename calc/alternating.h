
#ifndef CALC_ALTERNATING_
#define CALC_ALTERNATING_

#include "transformer.h"

namespace calc
{
   bool isatom( const logic::term& f );
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
      // We always create a conjunction, possibly consisting
      // of a single conjunct, but we do not create 
      // empty quantifiers.

   void 
   flatten_conj( logic::context& ctxt, const logic::term& f,
                 std::vector< logic::term > & into );

   logic::term
   splitalt( transformer& trans, logic::beliefstate& blfs,
             logic::context& ctxt, logic::term f,
             logic::selector op, unsigned int maxlevel );
      // op must be either kleene_or or kleene_and. 
}

#endif

