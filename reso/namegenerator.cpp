
#include "namegenerator.h"

namespace
{
   void increase( std::string& val )
   {
      const char first = '0';
      const char last = '9';
  
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


std::string reso::namegenerator::create( const std::string& base )
{
   auto p = bases. try_emplace( base, "00" ). first;

   auto res = base + ( p -> second );
   increase( p -> second );
   return res; 
}


void reso::namegenerator::print( std::ostream& out ) const
{
   out << "Namegenerator\n";
   for( const auto& p : bases )
      out << "   " << p. first << " : " << p. second << "\n";
   out << "\n";
}


