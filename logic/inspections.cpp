
#include "inspections.h"

void 
logic::debruijn_counter::operator( ) ( const term& t, size_t vardepth )
{
   // std::cout << "de Bruijn " << t << " / " << vardepth << "\n";

   if( t. sel( ) == op_debruijn )
   {
      auto v = t. view_debruijn( ). index( ); 

      // If we don't enter this if, the index is local, 
      // and we don't count it:

      if( v >= vardepth )
      {
         v -= vardepth; 
         ++ occ[v]; 
      }
   }
}

void logic::debruijn_counter::print( std::ostream& out ) const
{
   out << "DeBruijn Counter:\n";
   for( const auto& p : occ )
      out << "   #" << p. first << " : " << p. second << "\n";
}


void
logic::debruijn_cmp::operator( ) (  const term& t, size_t vardepth )
{
   if( t. sel( ) == op_debruijn )
   {
      auto ind = t. view_debruijn( ). index( );

      // If we don't enter this if, the index is local,
      // and we ignore it:

      if( ind >= vardepth )
      {
         ind -= vardepth;
         if( ind < nearest )
            nearest = ind;
      }
   }
}

void logic::debruijn_cmp::print( std::ostream& out ) const
{
   out << "Nearest DeBruijn:\n";
   out << "   #" << nearest;
}


