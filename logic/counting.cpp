
#include "counting.h"

void logic::debruijn_counter::operator( ) ( const term& t, size_t vardepth )
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
   out << "De Bruijn Counter:\n";
   for( const auto& p : occ )
      out << "   #" << p. first << " : " << p. second << "\n";
}

