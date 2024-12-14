
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
 
   void always_justification( const logic::beliefstate& bel );
   
#if 0
   void logicalsimplifications( ); 

   void kbo( );

   void replacements( );

   void betareduction( );
      // Test beta reduction, using Church numerals.
      // I am also interested in performance.

   void naturaldeduction( );

   void proofchecking( );

   void unification( );

   void tableau( );

   void tokenizer( );

   void parser( );
#endif
}

#endif
