
// Written by Hans de Nivelle, July 2025.

#ifndef CALC_PROOFCHECKING_
#define CALC_PROOFCHECKING_

#include "errorstack.h"
#include "sequent.h"
#include "proofterm.h"

namespace calc
{
   size_t nrsubforms( const logic::term& fm );
      // fm must be a Kleene operator.

   const logic::term& subform( const logic::term& fm, size_t i );
      // Get fm[i], fm must be a Kleene operator.

   logic::term replace( logic::term fm, size_t i, const logic::term& val );
      // Assign fm[i] := val, fm must be a Kleene operator.
 
   logic::term remove( logic::term fm, size_t i );
      // Remove i-th subformula. fm must be a Kleene operator. 
      // We move the subformulas after i one position back.
      // We could also swap with the last, which would be more efficient
      // (constant time), but we want to preserve order as much as possible.

   bool iscontradiction( const logic::term& fm );
      // True if fm counts as contradition.

   logic::term expanddef( const identifier& id, size_t& ind,
                          logic::term );
      // 
   logic::term 
   eval( const proofterm& prf, sequent& seq, errorstack& err );
      // In case of error, we express our frustration into err, and 
      // throw a failure exception.

}

#endif

