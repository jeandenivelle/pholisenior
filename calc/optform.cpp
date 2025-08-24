
#include "optform.h"
#include "logic/pretty.h"

#include "removelets.h"
#include "alternating.h"
#include "projection.h"

#include "logic/replacements.h"

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
      bld << kl. size( ) << " subforms in: ";
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

void calc::optform::aritymustbe( size_t i )
{  
   if( !fm. has_value( ))
      return;

   if( !fm. value( ). option_is_kleene( ))
      throw std::logic_error( "aritymustbe: Not a Kleene operator" );

   auto kl = fm. value( ). view_kleene( );

   if( kl. size( ) != i )
   {
      auto bld = errorheader( );
      bld << "formula must have arity " << i << ", but it is :";
      pretty( bld );
      err. push( std::move( bld ));
   
      fm. reset( );
   }
}

void calc::optform::nrvarsmustbe( size_t i )
{ 
   if( !fm. has_value( ))
      return;

   if( !fm. value( ). option_is_quant( ))
      throw std::logic_error( "nrvarsmustbe: Not a quantifier" );

   auto kl = fm. value( ). view_quant( );

   if( kl. size( ) != i )
   {
      auto bld = errorheader( );
      bld << "quantifier must have " << i << " variables, but it is : ";
      pretty( bld );
      err. push( std::move( bld ));
  
      fm. reset( );
   }
}

void calc::optform::make_anf2( )
{
   if( !fm. has_value( ))
      return;

   logic::context ctxt;
   fm. value( ) = removelets( seq, ctxt, fm. value( ));
   if( ctxt. size( ))
      throw std::logic_error( "context not empty" );

   fm. value( ) = alternating( fm. value( ), logic::op_kleene_and, 2 );
}

void calc::optform::normalize( )
{
   if( !fm. has_value( ))
      return;

   logic::betareduction beta;
   projection proj( seq.blfs );

   do
   {
      beta. counter = 0;
      rewr_outermost( beta );
   }
   while( beta. counter );
}

void calc::optform::quantify( const std::vector< logic::vartype > & vars )
{
   if( !fm. has_value( ))
      return;
   if( !vars. size( ))
      return; 

   if( !fm. value( ). option_is_kleene( ))
      throw std::logic_error( "quantify: Not a Kleene operator" );

   using namespace logic;

   auto kl = fm. value( ). view_kleene( );
   for( size_t i = 0; i != kl. size( ); ++ i )
   {
      auto repl = term( op_error );
         // kl. sub(i) will be replaced by repl at the end
         // of this block.

      if( fm. value( ). sel( ) == op_kleene_and )
         repl = term( op_kleene_forall, repl, vars. begin( ), vars. end( ));
      if( fm. value( ). sel( ) == op_kleene_or )
         repl = term( op_kleene_exists, repl, vars. begin( ), vars. end( ));

      auto replquant = repl. view_quant( );

      // As long as kl. sub(i) is the same quantifier, we
      // add the quantified variables to repl, and replace kl. sub(i)
      // by its body:

      while( kl. sub(i). sel( ) == repl. sel( ))
      {
         auto q = kl. sub(i). view_quant( );
         for( size_t v = 0; v != q. size( ); ++ v )
            replquant. push_back( q. var(v) ); 
         auto b = q. body( ); 
            // Without this separate b, code is unsafe.
         kl. update_sub( i, std::move(b) ); 
      }

      replquant. update_body( kl. extr_sub(i)); 
      kl. update_sub( i, std::move( repl )); 
   } 
}

void calc::optform::magic( )
{
   if( !fm. has_value( ))
      return; 

   auto bld = errorheader( );
   bld << "magically assuming :";
   bld << "DELETE THIS, IT IS UGLY\n";
   pretty( bld );
   err. push( std::move( bld ));
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

