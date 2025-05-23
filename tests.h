
#ifndef TESTS_
#define TESTS_   

#include "logic/context.h"
#include "logic/beliefstate.h"

namespace tests
{

   void add_settheory( logic::beliefstate& );

   void add_unique( logic::beliefstate& );

   void add_proof( logic::beliefstate& blfs );
   
   void transformations( logic::beliefstate& blfs ); 

#if 0
   void kbo( );
#endif
   
   void replacements( );

   void betareduction( );
      // Test beta reduction, using Church numerals.
      // I am also interested in performance.

   void proofchecking( logic::beliefstate& blfs );

#if 0
   void unification( );
#endif

   void pretty( const logic::beliefstate& blfs );

   void truthtables( );
      // check properties that can be checked by truth tables. 

   void parser( logic::beliefstate& blfs );
   
}

#endif
