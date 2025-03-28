
#include "beliefstate.h"
#include "termoperators.h"

logic::exact logic::beliefstate::append( belief&& bl )
{

   switch( bl. sel( ))
   {
   case bel_struct:
      {
         auto exstruct = exact( vect. size( ));
            // The exact name that the struct will have.

         structdefs[ bl. name( ) ]. push_back( exstruct );

         // We temporarily insert an empty belief, because we still need
         // access to bl. If we put in the vector already now, it moves 
         // with every insertion, which is annoying.

         vect. emplace_back( belief( bel_empty, identifier( ) ), 
                             dependencies( ));

         auto exconstr = exact( vect. size( ));
         functions[ bl. name( ) ]. push_back( exconstr );

         vect. emplace_back( belief( logic::bel_constr, bl. name( ), exstruct ), 
                             dependencies( ));

         // We also need to create the field functions:

         const structdef& sdef = bl. view_struct( ). def( ); 
            // sdef is not in vect. That would be dangerous.

         for( size_t offset = 0; offset != sdef. size( ); ++ offset )
         {
            auto fieldfunc = belief( logic::bel_fld, 
                                     sdef. at( offset ). name, 
                                     exstruct, offset );
            auto exfld = exact( vect. size( ));
            functions[ sdef. at( offset ). name ]. push_back( exfld ); 
            vect. emplace_back( std::move( fieldfunc ), dependencies( ));
         }

         at( exstruct ). first = std::move( bl );
         return exstruct;
      }      

   case bel_decl:
      {
         exact ex = exact( vect. size( ));
         functions[ bl. name( ) ]. push_back( ex );
         vect. emplace_back( std::move( bl ), dependencies( ));
         return ex; 
      }

   case bel_def:
      {
         exact ex = exact( vect. size( ));
         functions[ bl. name( ) ]. push_back( ex );
         vect. emplace_back( std::move( bl ), dependencies( ));
         return ex;
      }

   case bel_thm:
   case bel_asm:
   case bel_form:
      {
         exact ex = exact( vect. size( )); 
         formulas[ bl. name( ) ]. push_back( ex );
         vect. emplace_back( std::move( bl ), dependencies( ));
         return ex;
      }
      break;

   }

   std::cout << "dont know how to append : " << bl << "\n";
   throw std::runtime_error( "stopping" );
}


const std::vector< logic::exact > & 
logic::beliefstate::getstructdefs( const identifier& id ) const
{
   auto p = structdefs. find( id );
   if( p != structdefs. end( ))
      return p -> second;
   else
      return empty; 
}

const std::vector< logic::exact > & 
logic::beliefstate::getfunctions( const identifier& id ) const
{
   auto p = functions. find( id );
   if( p != functions. end( ))
      return p -> second;
   else
      return empty; 
}

const std::vector< logic::exact > & 
logic::beliefstate::getformulas( const identifier& id ) const
{
   auto p = formulas. find( id );
   if( p != formulas. end( ))
      return p -> second;
   else
      return empty;
}


namespace
{
   void print( std::ostream& out, const std::vector< logic::exact > & uses )
   {
      out << '{';
      for( auto p = uses. begin( ); p != uses. end( ); ++ p )
      {
         if( p != uses. begin( ))
            out << ", ";
         else
            out << " ";
         out << *p;
      }
      out << " }";
   }
}

void logic::beliefstate::print( std::ostream& out ) const
{
   out << "Beliefstate:\n"; 
   for( size_t i = 0; i != vect. size( ); ++ i )
      out << "   " << exact(i) << " : " << vect[i]. first << "\n";
   out << "\n";

   out << "Functions:\n";
   for( const auto& f : functions )
   {
      out << "   " << f. first << " :   ";
      ::print( out, f. second );
      out << '\n';
   }
   out << '\n';

   out << "Structdefs:\n";
   for( const auto& sdef : structdefs )
   {
      out << "   " << sdef. first << " :   ";
      ::print( out, sdef. second ); 
      out << '\n';
   }
   out << '\n';

   out << "Formulas:\n";
   for( const auto& f : formulas )
   {
      out << "   " << f. first << " :   ";
      ::print( out, f. second ); 
      out << '\n';
   }
   out << '\n';
}


