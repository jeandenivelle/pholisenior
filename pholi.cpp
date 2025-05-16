
#include "semantics/interpretation.h"

#include "errorstack.h"

#include "identifier.h"
#include "tests.h"

#include "logic/exact.h"
#include "logic/type.h"
#include "logic/position.h"
#include "logic/term.h"
#include "logic/context.h"
#include "logic/kbo.h"
#include "logic/pretty.h"
#include "logic/termoperators.h"

#include "logic/structural.h"
#include "logic/pretty.h"
#include "logic/replacements.h"

#include "parsing/tokenizer.h"

int main( int argc, char* argv[] )
{
   logic::beliefstate blfs; 
   tests::parser( blfs );
   std::cout << blfs << "\n";
   errorstack err;
   checkandresolve( blfs, err );
   std::cout << err << "\n";

   return 0;

   // tests::truthtables( );
   // return 0;

   tests::add_strict_prod( blfs ); 
   // tests::add_function( blfs );
   // tests::add_seq( blfs );
#if 0
   tests::add_unique( blfs );
#endif
   // tests::add_settheory( blfs );
   logic::pretty::print( std::cout, blfs ); 
   std::cout << "(before type checking)\n";

   // tests::structural( blfs );
   // tests::add_proof( blfs );

   logic::pretty::print( std::cout, blfs ); 
   std::cout << "(after type checking)\n";

   // tests::proofchecking( blfs );

   std::cout << blfs << "\n";

   // tests::pretty( blfs );
   return 0;

#if 0
   
   // tests::context( ); 
   // tests::setsimplifications( );
   // tests::kbo( );
   // tests::tokenizer( );
   // tests::betareduction( ); 
   // tests::proofpluscom( );
   // tests::replacements( );

   // tests::tableau( );
#endif

   return 0;
}


