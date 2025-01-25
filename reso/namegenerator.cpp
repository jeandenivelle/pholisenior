
#include "namegenerator.h"

namespace
{

   void increase( std::string& val )
   {
      constexpr char first = '0';
      constexpr char last = '9';
  
      size_t i = val. size( );
      while( i -- )
      {
         if( val[i] == last )
            val[i] = first;
         else
         {
            ++ val[i];
            return;
         }
      }
     
      val. insert( val. begin( ), first );
      ++ val. front( );
   }
}


std::string 
reso::namegenerator::next( )
{
   auto res = base + index;
   increase( index );
   return res; 
}


void reso::namegenerator::print( std::ostream& out ) const
{
   out << "Namegenerator:\n";
   out << "   " << base << " : " << index << "\n";
}


