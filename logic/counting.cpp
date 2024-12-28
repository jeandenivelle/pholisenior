
#include "counting.h"

void logic::debruijn_counter::operator( ) ( const term& t, size_t vardepth )
{
   std::cout << "de Bruijn " << t << " / " << vardepth << "\n";

   if( t. sel( ) == op_debruijn )
   {
      auto v = t. view_debruijn( ). index( ); 

      // Otherwise, the index is local, and we don't count it:

      if( v >= vardepth )
      {
         v -= vardepth; 
         ++ occ[v]; 
      }
   }
}

