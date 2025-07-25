
#include "sequent.h"
#include "logic/pretty.h"

logic::exact
calc::sequent::assume( std::string_view namebase, const logic::term& frm )  
{
   if( namebase. empty( )) 
      namebase = "form";

   auto id = get_fresh_ident( std::string( namebase ));
   std::cout << id << "\n";

   auto ex = blfs. append( logic::belief( logic::bel_form, id, frm ));
   steps. push_back( extension( seq_belief, ex, true ));
   return ex;
}

logic::exact
calc::sequent::assume( std::string_view namebase, const logic::type& tp )
{
   if( namebase. empty( ))
      namebase = "V";

   auto id = get_fresh_ident( std::string( namebase ));
   std::cout << id << "\n";

   auto ex = blfs. append( logic::belief( logic::bel_symbol, id, tp ));
   steps. push_back( extension( seq_belief, ex, true ));
   return ex;
}

logic::exact
calc::sequent::define( std::string_view namebase,
                       const logic::term& val, 
                       const logic::type& tp )
{
   auto freshid = identifier( ) + gen. create( std::string( namebase )); 
   auto def = logic::belief( logic::bel_def, freshid, val, tp );
   logic::exact ex = blfs. append( std::move( def )); 
   steps. push_back( extension( seq_belief, ex, true ));
   return ex;
}

logic::term
calc::sequent::getformula( logic::exact ex, errorstack& err ) const
{
   if( blfs. contains( ex ))
   {
      const auto& bel = blfs. at( ex );
      if( bel. sel( ) == logic::bel_thm )
         return bel. view_thm( ). frm( );

      if( bel. sel( ) == logic::bel_axiom )
         return bel. view_axiom( ). frm( );

      if( bel. sel( ) == logic::bel_form )
         return bel. view_form( ). frm( );
   }

   errorstack::builder bld;
   bld << "proof checking: name does not refer to formula " << ex << "\n";
   err. push( std::move( bld ));

   throw failure( );
}

identifier
calc::sequent::get_fresh_ident( std::string namebase ) 
{
   auto id = identifier( ) + gen. create( namebase );

   while( blfs. contains( id )) 
      id = identifier( ) + gen. create( namebase );

   return id;
}


#if 0
void
calc::sequent::addformula( std::string_view namebase,
                           const logic::term& f,
                           unsigned int par1, unsigned int par2,
                           unsigned int br, unsigned int nr )
{
   if( namebase. empty( ))
      throw std::logic_error( "new formula: namebase cannot be empty" );

   auto name = get_fresh_ident( namebase );
   auto ex = blfs. append( logic::belief( logic::bel_form, name, f ));
   bool anf = isinanf(f); 
   size_t rank = 0;
   if( anf )
   {
      rank = alternation_rank(f);
   }
   ext. push_back( extension( ext_initial, false, "", 
                              ex, f, anf, rank, par1, par2, br, nr ));
}

#endif

void calc::sequent::restore( size_t ss )
{
   // If anything got blocked, we unblock it:

   while( ss < steps. size( )) 
   {
      switch( steps. back( ). sel( ))
      {
      case seq_belief:
         {
            auto bl = steps. back( ). view_belief( );
            blfs. backtrack( bl. name( ));
         }
         break;
      case seq_blocking:
         {
            size_t nr = steps. back( ). view_blocking( ). nr( );
            steps[ nr ]. view_belief( ). visible( ) = true;
         }
         break;
      }
      steps. pop_back( );
   }
}

void calc::sequent::pretty( std::ostream& out, bool showblocked ) const
{
   out << "Sequent:\n";
   for( const auto& e : steps )
   {
      switch( e. sel( ))
      {
      case seq_belief:
         {
            auto bl = e. view_belief( ); 
            if( showblocked || bl. visible( ))
            { 
               out << "   " << blfs. at( bl. name( ) ). ident( );
               logic::pretty::print( out, blfs, blfs. at( bl. name( ) )); 
            } 
         }
         break; 
      default: 
         std::cout << e. sel( ) << "\n";
         throw std::runtime_error( "doesnt know how to be pretty" );
      }
   }
}


