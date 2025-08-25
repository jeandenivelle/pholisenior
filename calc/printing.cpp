
#include "printing.h"
#include "logic/pretty.h"


errorstack::builder
calc::printing::makeheader( const sequent& seq, std::string_view rule )
{
   errorstack::builder bld;
   for( unsigned int i = 0; i < 60; ++ i )
      bld. put( '-' );
   bld. put( '\n' );

   bld << "Error applying " << rule << ":\n";
   bld << seq << "\n";
   return bld;
}

void
calc::printing::pretty( std::ostream& out, 
                        const sequent& seq, const logic::type& tp )
{
   logic::pretty::print( out, seq. blfs, tp, {0,0} );
}

void
calc::printing::pretty( std::ostream& out, 
                        const sequent& seq, const logic::term& tm )
{
   logic::context ctxt;
   logic::pretty::print( out, seq. blfs, ctxt, tm );
}

const char*
calc::printing::viewpretty( logic::selector op )
{
   switch( op )
   {
   case logic::op_kleene_or:
      return "kleene-or";
   case logic::op_kleene_and:
      return "kleene-and";
   case logic::op_kleene_forall:
      return "kleene-forall";
   case logic::op_kleene_exists:
      return "kleene-exists";
   }
   return "???";
}


