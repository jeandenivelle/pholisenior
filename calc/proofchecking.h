
// Written by Hans de Nivelle, July 2025.

#ifndef CALC_PROOFCHECKING_
#define CALC_PROOFCHECKING_

#include "errorstack.h"
#include "sequent.h"
#include "proofterm.h"

namespace calc
{

   logic::term 
   eval( const proofterm& prf, sequent& seq, errorstack& err );
      // In case of error, we express our frustration into err, and 
      // throw a failure exception.


}

#endif

