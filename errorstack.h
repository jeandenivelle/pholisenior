
// Written by Hans de Nivelle, Nov. 2024.

#ifndef ERRORSTACK_
#define ERRORSTACK_

#include <string>
#include <vector>
#include <iostream> 
#include <sstream>

#include "util/indentation.h"


struct error
{
   enum level { warning, serious, header };

   std::ostringstream top;
   level lev;  
   mutable bool reported;
      // Meaning is: Everyting that we have, has been reported.

   // We have no nice interface, because we expect to be called only
   // from errorstack.

   explicit error( level lev ) :
      lev( lev ),
      reported( true )    // Because we have nothing.
   { }

   error( error&& other ) noexcept
   {
      top = std::move( other. top ); other. top. clear( );
      lev = other. lev; 
      reported = other. reported; other. reported = true; 
   }

   error& operator = ( const error& ) = delete;
  
   void print( std::ostream& out ) const;

   ~error( )
   {
      if( !reported )
         print( std::cout );
   }
 
   template< typename T > std::ostream& operator << ( const T& t )
   {
      top << t;
      reported = false;
      return top;
   }
};


class errorstack
{
   std::vector< error > vect;
   std::vector< size_t > sub;
      // This data structure is internally a bit weird, but 
      // convenient to use: vect[i] can be a header with suberrors.
      // These errors are stored in the interval [ sub[i], i ).
      // If there are no suberrors, then sub[i] = i.

   void 
   print( indentation ind, size_t pos1, size_t pos2, std::ostream& out ) const;
      // Prints the errors in [ pos1, ... pos2 > 

   void print( indentation ind, size_t pos, std::ostream& out ) const;

public:
   errorstack( ) noexcept = default;
   errorstack( errorstack&& ) noexcept = default;
   errorstack& operator = ( errorstack&& ) noexcept = default;

   void extend( const std::string& cause = "",
                error::level lev = error::serious )
   { 
      sub. push_back( vect. size( ));

      vect. push_back( error( lev ) ); 
      if( !cause. empty( ))
         vect. back( ) << cause;
   }

   void extend( error::level lev )
      { extend( "", lev ); }


   void addheader( size_t start, const std::string& place = "" )
   {
      vect. push_back( error( error::header ));
      if( !place. empty( ))
         vect. back( ) << place;
      sub. push_back( start );
   }

   error& back( ) 
      { return vect. back( ); }

   const error& back( ) const
      { return vect. back( ); }

   size_t size( ) const 
      { return vect. size( ); }

   void print( std::ostream& out ) const
      { print( indentation( ), 0, size( ), out ); }
};

#endif

