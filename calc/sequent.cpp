
#include "sequent.h"
#include "logic/pretty.h"

logic::exact
calc::sequent::push( std::string_view namebase, logic::term frm )  
{
   if( namebase. empty( )) 
      namebase = "assume";

   auto id = get_fresh_ident( std::string( namebase ));
   std::cout << id << "\n";

   auto ex = blfs. append( logic::belief( logic::bel_form, id, frm ));
   steps. push_back( extension( seq_form, ex, true ));
   return ex;
}


logic::term
calc::sequent::getformula( logic::exact ex )
{
   if( blfs. contains( ex ))
   {
      const auto& bel = blfs. at( ex );
      if( bel. sel( ) == logic::bel_thm )
         return bel. view_thm( ). frm( );

   }

   throw std::logic_error( "name not found" );
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

void calc::sequent::pretty( std::ostream& out, bool showhidden ) const
{
   out << "Sequent:\n";
   for( const auto& e : steps )
   {
      if( showhidden || e. visible( ))
      {
         switch( e. sel( ))
         {
         case seq_form:
            {
               auto name = e. name( );
               out << blfs. at( name ). name( );
               logic::pretty::print( out, blfs, blfs. at( name )); 
               break;
            } 
         
         default: 
            std::cout << e. sel( ) << "\n";
            throw std::runtime_error( "doesnt know how to be pretty" );
         }
      }
   }
}


