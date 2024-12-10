
#include "uniquenamestack.h"
#include <iomanip>
#include "util/print.h"

namespace
{

   void reduce2base( std::string& s )
   {
      while( s. size( ) && isdigit( s. back( )))
         s. pop_back( );

      if( s. size( ) == 0 )
         s. push_back( 'V' );  
   }

   void addindex( std::string& root, unsigned int index )
   {
      unsigned int digit10 = 1;
      while( digit10 <= index )
         digit10 *= 10;
      digit10 /= 10;

      while( digit10 != 0 )
      {
         root += '0' + ( index / digit10 );
         index %= digit10;
         digit10 /= 10;
      }   
   }

   size_t indexstart( const std::string& s ) 
   {
      size_t start = s. size( );
      while( start != 0 && isdigit( s[ start - 1 ] ))
         -- start;

      return start;
   }
}

auto logic::pretty::uniquenamestack::extend( std::string name )
   -> const uniquename&
{
   reduce2base( name );

   auto& uses = bases[ name ];
   size_t ind = uses. size( ); 
   uses. push_back( vect. size( ));
   vect. push_back( uniquename( name, ind ) );
   return vect. back( );
}

auto logic::pretty::uniquenamestack::nextname( std::string name ) const 
   -> uniquename 
{
   reduce2base( name );

   // We do this, instead of just [], so that we can be const.

   size_t ind = 0;
   if( auto p = bases. find( name ); p != bases. end( ))
      ind = p -> second. size( );

   return uniquename( name, ind );
}

void logic::pretty::uniquenamestack::restore( size_t s )
{
   while( vect. size( ) > s )
   {
      bases. at( vect. back( ). base ). pop_back( ); 
      vect. pop_back( );
   }
}

size_t
logic::pretty::uniquenamestack::find( const std::string& s ) const
{
   size_t start = indexstart(s);

   // We don't allow leading zeroes of the index:

   if( start < s. size( ) && s[ start ] == '0' )
      return size( ); 

   size_t index = 0; 

   while( start < s. size( ))
   {
      index = 10 * index + ( s[ start ] - '0' ); 
      ++ start;
   }

   std::string base = s;
   reduce2base( base ); 
   auto p = bases. find( base );
   if( p == bases. end( ) || index >= p -> second. size( )) 
      return size( ); 
   else
      return size( ) - 1 - ( p -> second[ index ] ); 
}

void 
logic::pretty::uniquenamestack::print( std::ostream& out ) const
{
   for( long int ind = 1 - size( ); const auto& u : vect ) 
   {
      out << '#' << ind << " : ";
      out << u << "\n";

      ++ ind;
   }
}

