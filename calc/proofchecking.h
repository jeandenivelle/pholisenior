
// Written by Hans de Nivelle, July 2025.

#ifndef CALC_PROOFCHECKING_
#define CALC_PROOFCHECKING_

#include "errorstack.h"
#include "sequent.h"
#include "proofterm.h"

namespace calc
{

   const logic::term&
   get_conjunct( const logic::term& fm, size_t ind, errorstack& err );
      // If fm is not a conjunction, or ind is too big, we write
      // an error, and throw failure.

   const logic::term&
   get_disjunct( const logic::term& fm, size_t ind, errorstack& err );

   bool iscontradiction( const logic::term& fm );
      // True if fm counts as contradition.

   logic::term 
   eval( const proofterm& prf, sequent& seq, errorstack& err );
      // In case of error, we express our frustration into err, and 
      // throw a failure exception.

}

#endif

