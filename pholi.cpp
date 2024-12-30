
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
#include "logic/replacements.h"
#include "logic/counting.h"

#include "reso/transformations.h"
#include "reso/namegenerators.h"

int main( int argc, char* argv[] )
{
   logic::beliefstate blfs;
   reso::namegenerators gen;
   std::cout << gen << "\n";

   logic::context ctxt;

   ctxt. append( "aa", logic::type( logic::type_unchecked, 
                                    identifier( ) + "three" ));
   ctxt. append( "aa", logic::type( logic::type_truthval ));
   ctxt. append( "aa", logic::type( logic::type_obj ));
   ctxt. append( "aa", logic::type( logic::type_obj ));

   auto fm = 2_db && 3_db;
   std::cout << fm << "\n";

   fm = introduce_predicate( blfs, gen, ctxt, std::move(fm));
   return 0;

   // tests::replacements( );
   // return 0;

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
   std::cout << blfs << "\n";
   tests::structural( blfs );
   tests::add_proof( blfs );

   std::cout << blfs << "\n";
   std::cout << "(after checking)\n";

   tests::transformations( blfs );
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


