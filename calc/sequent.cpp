
#include "sequent.h"
#include "alternating.h"
#include "logic/pretty.h"

logic::exact 
calc::sequent::add_initial( selector sel, 
                            std::string_view namebase,
                            logic::term goal )  
{
   if( namebase. empty( )) 
   {
      switch( sel ) 
      {
      case ext_truth:
         namebase = "neggoal";
         break; 
      case ext_prop: 
         namebase = "negprop";
         break;
      default:
         namebase = "initial";
         break; 
      }
   }


   switch( sel )
   {
   case ext_truth:
      goal = logic::term( logic::op_not, goal );
      break;
   case ext_prop:
      goal = logic::term( logic::op_not, 
               logic::term( logic::op_prop, goal ));
      break;
   default:
      throw std::logic_error( "unknown initial type" );
   }

   std::cout << goal << "\n";

   auto id = get_fresh_ident( std::string( namebase ));
   std::cout << id << "\n";

   auto ex = blfs. append( logic::belief( logic::bel_form, id, goal ));
   steps. push_back( extension( sel, true, ex ));
   return ex; 
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
         case ext_prop:
         case ext_truth: 
            {
               auto name = e. view_initial( ). ex( ); 
               out << e. sel( ) << " " << blfs. at( name ). name( );
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


