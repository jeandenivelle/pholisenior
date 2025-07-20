
#ifndef CALC_ALTERNATING_
#define CALC_ALTERNATING_

#include <vector>

#include "logic/term.h"
#include "logic/context.h"

namespace calc
{
   bool haskleene( const logic::term& f );
      // True if main operator is a Kleene operator.
      // Negation and prop do not count as Kleene operator.

   logic::selector quantof( logic::selector op );
      // Returns the quantifier that belongs to op.
      // op_kleene_or  -> op_kleene_exists
      // op_kleene_and -> op_kleene_forall

   logic::selector alternation( logic::selector op );
      // Returns the alternation of op.
      // op_kleene_or -> op_kleene_and
      // op_kleene_and -> op_keene_or

   // Result will be a disjunction of exists of alt_foralls( ).

   logic::term
   alternating( const logic::term& fm, 
                logic::selector op, unsigned int rank );
      // op must be op_kleene_and, or op_kleene_or.

   void 
   flatten( logic::context& ctxt, const logic::term& f,
            logic::selector op, unsigned int rank, 
            std::vector< logic::term > & into );

   bool isalternating( const logic::term& f,
                       logic::selector op, unsigned int rank );
      // The alternation rank of f. 

#if 0
   logic::term
   restrict_alternation( transformer& trans, logic::beliefstate& blfs,
             logic::context& ctxt, logic::term f,
             logic::selector op, unsigned int maxrank );
      // op must be a Kleene operator. 
#endif

}

#endif

