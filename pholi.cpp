
#include "semantics/interpretation.h"

#include "errorstack.h"
#include "filehasher.h"

#include "identifier.h"
#include "tests.h"

#include "logic/exact.h"
#include "logic/structural.h"
#include "logic/pretty.h"
#include "logic/termoperators.h"

#include "parsing/parser.h"

void
includefile( logic::beliefstate& blfs, 
             filehasher& seen, const std::filesystem::path& file,
             errorstack& err ) 
{
   if( !exists( file ))
   {
      errorstack::builder bld;
      bld << "file " << file. string( ) << " does not exist";
      err. push( std::move( bld ));
      return;
   }

   // If the file was read already, we ignore it:

   if( !seen. insert( file ))
      return;
 
   std::cout << "file " << file << " is new and will be read\n";

   // We checked existence of file, but one never knows ...

   std::ifstream in( file );
   if( !in )
   {
      errorstack::builder bld; 
      bld << "could not open file " << file. string( ) << "\n";
      err. push( std::move( bld ));  
      return; 
   }

   lexing::filereader inp( &in, file );

   parsing::tokenizer tok( std::move( inp ));
   parsing::parser prs( tok, blfs );

   prs. debug = 0;
   prs. checkattrtypes = 0;

   errorstack::builder bld;

   auto res = prs. parse( parsing::sym_File, bld );

   if( bld. view( ). size( ))
   {
      size_t s = err. size( );
      err. push( std::move( bld ));

      errorstack::builder header;
      header << "there were parse errors in file "
             << file. string( ) << ": ";
      err. addheader( s, std::move( header ));       
   }

}


int main( int argc, char* argv[] )
{
   errorstack err;

   logic::beliefstate blfs;  
   filehasher seen;
   includefile( blfs, seen, "examples/standard.phl", err ); 
   includefile( blfs, seen, "aa1", err );
   includefile( blfs, seen, "examples/natural.phl", err );
   // includefile( blfs, "examples/automata.phl" );

   seen. print( std::cout );

   std::cout << "(before type checking)\n";
   std::cout << blfs << "\n";

   checkandresolve( blfs, err );
   std::cout << "(after type checking)\n";

   std::cout << blfs << "\n";

   // tests::clausify( blfs, err );

   // tests::truthtables( );

   // tests::add_function( blfs );
   // tests::add_seq( blfs );

   // tests::add_proof( blfs );

   // tests::proofchecking( blfs, err );
   std::cout << err << "\n";

   tests::kbo( blfs );
   return 0;

#if 0
   // tests::context( ); 
   // tests::setsimplifications( );
   // tests::betareduction( ); 
   // tests::proofpluscom( );
   // tests::replacements( );

   // tests::tableau( );
#endif

   return 0;
}


