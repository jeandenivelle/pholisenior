
// Written by Hans de Nivelle, Nov. 2024.
// Changed the interface on 12.12.2024.

#ifndef ERRORSTACK_
#define ERRORSTACK_

#include <string>
#include <vector>
#include <iostream> 
#include <sstream>

#include "util/indentation.h"


struct error
{
   enum seriousness { warning, serious, header };

   std::string top;
   seriousness ser;  
   mutable bool reported;
      // Meaning is: Everyting that we have, has been reported.

   // We have no nice interface, because we expect to be called only
   // from errorstack.

   error( const std::string& top, seriousness ser ) 
      : top( top ), 
        ser( ser ),
        reported( top. empty( )) 
   { }

   error( std::string&& top, seriousness ser ) 
      : top( std::move( top )),
        ser( ser ) 
   { reported = this -> top. empty( ); }

   error( const char* top, seriousness ser )
      : top( std::string( top )),
        ser( ser ),
        reported( ! *top )
   { }

   error( error&& other ) noexcept
   {
      top = std::move( other. top ); other. top. clear( );
      ser = other. ser; 
      reported = other. reported; other. reported = true; 
   }

   error& operator = ( const error& ) = delete;
  
   void print( std::ostream& out ) const;

   ~error( )
   {
      if( !reported && !top. empty( ))
         print( std::cout );
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

   void push( const std::string& meh, 
              error::seriousness ser = error::serious )
   { 
      sub. push_back( vect. size( ));
      vect. emplace_back( meh, ser ); 
   }

   void push( std::string&& meh,
              error::seriousness ser = error::serious )
   {
      sub. push_back( vect. size( ));
      vect. emplace_back( std::move( meh ), ser );
   }

   void push( const char* meh,
              error::seriousness ser = error::serious )
   {
      sub. push_back( vect. size( ));
      vect. emplace_back( meh, ser );
   }


   using builder = std::ostringstream;
      // You can whine into the builder, and push the builder
      // when you're done. 

   void push( builder& meh, 
              error::seriousness ser = error::serious )
   {
      sub. push_back( vect. size( ));
      vect. emplace_back( meh. str( ), ser );
   }

   void push( builder&& meh,
              error::seriousness ser = error::serious )
   {
      sub. push_back( vect. size( ));
      vect. emplace_back( std::move(meh). str( ), ser );
   }

   void addheader( size_t start, const std::string& header )
   {
      vect. emplace_back( header, error::header );
      sub. push_back( start );
   }

   size_t size( ) const 
      { return vect. size( ); }

   bool isempty( ) const 
      { return vect. empty( ); }

   void print( std::ostream& out ) const
      { print( indentation( ), 0, size( ), out ); }
};

#endif

