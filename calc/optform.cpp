
#include "optform.h"
#include "logic/pretty.h"

errorstack::builder
calc::optform::errorheader( )
{
   errorstack::builder bld;
   for( unsigned int i = 0; i < 60; ++ i )
      bld. put( '-' );
   bld. put( '\n' );

   bld << "Error applying " << rule << ":\n";
   bld << seq << "\n";
   return bld;
}

void calc::optform::musthave( logic::selector op )
{
   if( !fm. has_value( ))
      return; 
   
   if( fm. value( ). sel( ) == op )
      return;

   errorstack::builder bld;
   bld << "wrong operator for " << rule << " : ";
   bld << "main operator must be " << pretty( op );
   bld << ", but the formula is: ";
   pretty( bld );
   err. push( std::move( bld ));

   fm. reset( ); 
}


void calc::optform::getsub( size_t i ) 
{
   if( !fm. has_value( ))
      return; 

   if( !fm. value( ). option_is_kleene( ))
      throw std::logic_error( "getsub: Not a Kleene operator" );

   auto kl = fm. value( ). view_kleene( );

   if( i >= kl. size( ))
   {
      auto bld = errorheader( );
      bld << "need subform nr " << i << ", but there are only ";
      bld << kl. size( ) << " in: ";
      pretty( bld );
      err. push( std::move( bld ));
      fm. reset( );
      return;
   }
   
   fm = kl. extr_sub(i);
}


void calc::optform::getuniquesub( ) 
{
   if( !fm. has_value( ))
      return;

   if( !fm. value( ). option_is_kleene( ))
      throw std::logic_error( "getuniquesub: Not a Kleene operator" );

   auto kl = fm. value( ). view_kleene( );

   if( kl. size( ) != 1 )
   {
      auto bld = errorheader( );
      bld << "formula must have arity one, but it is :";
      pretty( bld );
      err. push( std::move( bld ));

      fm. reset( );
      return;
   }

   fm = kl. extr_sub(0);
}


void calc::optform::print( std::ostream& out ) const
{
   if( fm. has_value( ))
      out << rule << " : " << fm. value( );
   else
      out << rule << " : " << "(no formula)";
   out << "\n";
}

void calc::optform::pretty( std::ostream& out ) const
{
   if( fm. has_value( ))
   {
      logic::context ctxt;
      logic::pretty::print( out, seq. blfs, ctxt, fm. value( ));
   }
   else
      out << "(no formula)";

   out << "\n";
}

const char* calc::optform::pretty( logic::selector op )
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

