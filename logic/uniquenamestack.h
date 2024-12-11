
// Written by Hans de Nivelle, probably Spring 2023.

#ifndef LOGIC_PRETTY_UNIQUENAMESTACK_
#define LOGIC_PRETTY_UNIQUENAMESTACK_

#include <iostream>
#include <vector>
#include <string>
#include <unordered_map>

namespace logic {
namespace pretty   
{

   struct uniquename
   {
      std::string base;
      size_t index;

      uniquename( ) = delete;
      uniquename( const std::string& base, size_t index )
         : base( base ), index( index ) 
      { }

      uniquename( std::string&& base, size_t index )
         : base( std::move( base )), index( index )
      { }

      void print( std::ostream& out ) const 
      {
         if( index ) 
            out << base << index;
         else
            out << base; 
      }
   };


   class uniquenamestack
   {
      std::vector< uniquename > vect; 
      std::unordered_map< std::string, std::vector< size_t >> bases;
         // Lists the occurrences of a name prefix (as indices of vect).
       
   public:
      uniquenamestack( ) noexcept = default;
      uniquenamestack( uniquenamestack&& ) noexcept = default;
      uniquenamestack& operator = ( uniquenamestack&& ) noexcept = default; 

      size_t size( ) const { return vect. size( ); } 

      void restore( size_t s );

      // Correctly looks up a De Bruijn index:

      const uniquename& getname( size_t index ) const
         { return vect[ vect. size( ) - index - 1 ]; }

      const uniquename& extend( std::string name );
      
      uniquename nextname( std::string name ) const;
         // Get the uniquename that would be created if 
         // extend( name ) would be called, without 
         // actually extending. 

      size_t find( const std::string& s ) const;
         // Returns size( ) if we don't know about s. 
         // Otherwise, a De Bruijn index, which can be used
         // as argument to getname( ).  

      bool issafe( std::string s ) const;
         // True if a name is safe, which means that it does
         // not conflict with a name that we have.
         // We need to pass by value because we remove the index.
                   
      void print( std::ostream& out ) const;
   };

}}


#endif


