
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

#include "parsing/parser.h"

void readfromfile( logic::beliefstate& blfs, const std::string& name ) 
{ 
   std::ifstream in( name );
   if( !in )
   {
      std::cout << "the file is: " << name << "\n";
      throw std::runtime_error( "could not open it" );
   }
 
   lexing::filereader inp( &in, name );

   parsing::tokenizer tok( std::move( inp ));
   parsing::parser prs( tok, blfs );

   prs. debug = 0;
   prs. checkattrtypes = 0;

   auto res = prs. parse( parsing::sym_File );
}


int main( int argc, char* argv[] )
{
   logic::beliefstate blfs;  
   readfromfile( blfs, "examples/strict_prod.phl" ); 
   readfromfile( blfs, "examples/natural.phl" );
   readfromfile( blfs, "examples/automata.phl" );

   errorstack err;

   checkandresolve( blfs, err );
   std::cout << err << "\n";
   std::cout << blfs << "\n";
   return 0;

   // tests::truthtables( );
   // return 0;

   // tests::add_function( blfs );
   // tests::add_seq( blfs );
#if 0
   tests::add_unique( blfs );
#endif
   // tests::add_settheory( blfs );
   std::cout << "(before type checking)\n";

   // tests::structural( blfs );
   // tests::add_proof( blfs );

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


