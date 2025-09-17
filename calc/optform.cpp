
#include "optform.h"
#include "printing.h"

#include "removelets.h"
#include "alternating.h"
#include "projection.h"

#include "logic/replacements.h"


void calc::optform::musthave( logic::selector op )
{
   if( !fm. has_value( ))
      return; 
   
   if( fm. value( ). sel( ) == op )
      return;

   errorstack::builder bld;
   bld << "wrong operator for " << rule << " : ";
   bld << "main operator must be " << printing::viewpretty( op );
   bld << ", but the formula is: ";
   pretty( bld );
   err. push( std::move( bld ));

   fm. reset( ); 
}


void calc::optform::replacebysub( size_t i ) 
{
   if( !fm. has_value( ))
      return; 

   if( !fm. value( ). option_is_kleene( ))
      throw std::logic_error( "replacebysub: Not a Kleene operator" );

   auto kl = fm. value( ). view_kleene( );

   if( i >= kl. size( ))
   {
      auto bld = printing::makeheader( seq, rule );
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
      auto bld = printing::makeheader( seq, rule );
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
      auto bld = printing::makeheader( seq, rule );
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
      auto bld = printing::makeheader( seq, rule );
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

void calc::optform::fake( )
{
   if( !fm. has_value( ))
      return; 

   auto bld = printing::makeheader( seq, rule );
   bld << "faked proof of:  ";
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
      printing::pretty( out, seq, fm. value( )); 
   else
      out << "(no formula)";

   out << "\n";
}


