
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
calc::namegenerator::create( std::string base )
{
   while( !base. empty( ) && isdigit( base. back( )) )
      base. pop_back( );
   
   auto p = names. find( base );
   if( p == names. end( ))
   {
      p = names. insert( 
             std::pair< std::string, std::string > ( base, "0001" )). first;
   }
   base += ( p -> second );
   increase( p -> second );
   return base;
}

void calc::namegenerator::print( std::ostream& out ) const
{
   out << "Namegenerator:\n";
   for( const auto& n : names )
      out << "   " << n. first << " : " << n. second << "\n";
}


