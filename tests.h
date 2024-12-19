
#ifndef TESTS_
#define TESTS_   

#include "logic/context.h"
#include "logic/beliefstate.h"

namespace tests
{

   void add_strict_prod( logic::beliefstate& );
      // Define the strictness predicates.

   void add_settheory( logic::beliefstate& );

   void add_seq( logic::beliefstate& );
      // Add Seq and natural numbers. 

   void add_function( logic::beliefstate& );
      // Add function (2.6).

   void add_unique( logic::beliefstate& );

   void structural( logic::beliefstate& );
      // Tests for structural type checking.
 
   void add_proof( logic::beliefstate& bel );
   
   void transformations( logic::beliefstate& blfs ); 

#if 0
   void kbo( );
#endif

   void replacements( );

   void betareduction( );
      // Test beta reduction, using Church numerals.
      // I am also interested in performance.
#if 0
   void proofchecking( );

   void unification( );

   void tableau( );

   void tokenizer( );

   void parser( );
#endif
}

#endif
