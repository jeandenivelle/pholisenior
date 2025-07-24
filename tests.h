
#ifndef TESTS_
#define TESTS_   

#include "logic/context.h"
#include "logic/beliefstate.h"
#include "errorstack.h"

namespace tests
{
   void add_settheory( logic::beliefstate& blfs );

   void clausify( logic::beliefstate& blfs, errorstack& err );

#if 0
   void kbo( );
#endif

   void betareduction( logic::beliefstate& blfs, errorstack& err );
      // Test beta reduction, using Church numerals.
      // I am also interested in performance.

   void proofchecking( logic::beliefstate& blfs, errorstack& err );

#if 0
   void unification( );
#endif

   void pretty( const logic::beliefstate& blfs );

   void truthtables( );
      // check properties that can be checked by truth tables. 

   void parser( logic::beliefstate& blfs );
   
}

#endif
