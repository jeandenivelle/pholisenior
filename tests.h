
#ifndef TESTS_
#define TESTS_   

#include "errorstack.h"
#include "logic/context.h"
#include "logic/beliefstate.h"

namespace tests
{
   void add_settheory( logic::beliefstate& blfs );

   void clausify( logic::beliefstate& blfs, errorstack& err );

   void simplify( );

   void cmp( );

   void betareduction( logic::beliefstate& blfs, errorstack& err );
      // Test beta reduction, using Church numerals.
      // I am also interested in performance.

   void smallproofs( logic::beliefstate& blfs, errorstack& err );
   void bigproof( logic::beliefstate& blfs, errorstack& err );

   void unification( const logic::beliefstate& blfs, errorstack& err );

   void pretty( const logic::beliefstate& blfs );

   void truthtables( );
      // check properties that can be checked by truth tables. 

   void parser( logic::beliefstate& blfs );
   
}

#endif
