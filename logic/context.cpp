
#include "context.h"

void logic::context::restore( size_t s )
{
   while( vect. size( ) > s )
      vect. pop_back( );
}

void logic::context::print( std::ostream& out ) const
{
   out << "Context:\n";
   for( ssize_t ind = 1 - size( ); const auto& b : vect ) 
   {
      out << "   #" << ind << " : ";
      out << b. first << "    " << b. second << "\n";

      ++ ind;
   }
}

