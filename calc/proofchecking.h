
// Written by Hans de Nivelle, July 2025.

#ifndef CALC_PROOFCHECKING_
#define CALC_PROOFCHECKING_

#include "errorstack.h"
#include "sequent.h"
#include "proofterm.h"

namespace calc
{


   logic::term 
   eval( sequent& seq, const proofterm& prf, errorstack& err );
      // In case of error, we complain into err, and 
      // throw a failure exception.

}

#endif

