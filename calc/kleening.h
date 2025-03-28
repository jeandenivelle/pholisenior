
#ifndef CALC_KLEENING_
#define CALC_KLEENING_

#include "polarity.h"
#include "logic/term.h"


namespace calc
{
   logic::selector kleening( logic::selector op );
      // Get the kleening of op, for a monotone operator.

   // blfs is not constant, because we may add predicate declarations.

   logic::term knf( const logic::term& f, polarity pol );
   logic::term knf_prop( const logic::term& f, polarity pol );

}

#endif

