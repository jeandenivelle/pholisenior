
#include "semantics/truthval.h"

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

#include "calc/namegenerator.h"

int main( int argc, char* argv[] )
{
   std::cout << semantics::ff << "\n";
   return 0;

   std::unordered_map< identifier, identifier::hash, identifier::equal_to, int > test;

   logic::beliefstate blfs;

   // logic::beliefstate blfs; 
   tests::add_strict_prod( blfs ); 
#if 0
   tests::add_function( blfs );
#endif
   tests::add_seq( blfs );
#if 0
   tests::add_unique( blfs );
#endif
   tests::add_settheory( blfs );
   logic::pretty::print( std::cout, blfs ); 
   std::cout << "(before type checking)\n";

   tests::structural( blfs );
   // tests::add_proof( blfs );

   logic::pretty::print( std::cout, blfs ); 
   std::cout << "(after type checking)\n";

   tests::transformations( blfs );
   return 0;

   tests::pretty( blfs );
   return 0;

#if 0
   
   // tests::context( ); 
   // tests::setsimplifications( );
   // tests::kbo( );
   // tests::tokenizer( );
   // tests::betareduction( ); 
   // tests::naturaldeduction( ); 
   // tests::proofpluscom( );
   // tests::replacements( );

   // tests::tableau( );
#endif

   return 0;
}


