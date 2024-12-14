
#include "errorstack.h"

#include "identifier.h"
#include "tests.h"

#include "logic/exact.h"
#include "logic/type.h"
#include "logic/position.h"
#include "logic/term.h"
#include "logic/context.h"
#include "logic/kbo.h"
#include "logic/termoperators.h"

#include "logic/structural.h"
#include "logic/pretty.h"

int main( int argc, char* argv[] )
{

   logic::beliefstate bel;

   tests::add_strict_prod( bel ); 
#if 0
   tests::add_function( bel );
#endif
   tests::add_seq( bel );
#if 0
   tests::add_unique( bel );
   tests::add_settheory( bel );
#endif
   std::cout << bel << "\n";
   tests::structural( bel );
#if 0
   auto truth = logic::type( logic::type_truthval );
   auto obj = logic::type( logic::type_obj );
   auto nat = logic::type( logic::type_ident, identifier( ) + "natgen" );

   auto ff = logic::type( logic::type_func, truth, { obj, truth } );
   ff = logic::type( logic::type_func, ff, { } ); 
   std::cout << ff << "\n";

   auto state = tests::always_justification( bel );
   std::cout << state << "\n";
#endif

   return 0;

#if 0
   auto tm = 44_db && "aaa"_inexact;
   tm = apply( "field"_inexact, { tm } );

   std::cout << implies( tm, tm ) << "\n";
  
   auto lab = logic::term( logic::op_named, tm, identifier( ) + "thm1" );

   std::cout << lab << "\n";
   return 0;
   
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


