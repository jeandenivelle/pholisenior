
#ifndef SEMANTICS_FUNCTION_
#define SEMANTICS_FUNCTION_

#include <vector>
#include <iostream>

#include "value.h"

namespace semantics
{

   struct function
   {
      using sized_type = std::pair< primtype, unsigned int > ; 
         // A pair consisting of a primitive type, together with its size. 
         // It is always 2 or 3 for prim_truthval.

      std::vector< sized_type > argtypes;

      sized_type restype;
      
      std::vector< unsigned int > values;

      function( ) = delete;  
      function( const std::vector< sized_type > & argtypes, 
                sized_type restype );

      function( std::vector< sized_type > && argtypes, sized_type restype );
      function( const std::vector< sized_type > & argtypes, sized_type restype,
                std::initializer_list< unsigned int > values );
     
      function( function&& ) = default;
      function& operator = ( function&& ) = default;
 
      size_t domain_size( ) const;
      bool allzeroes( ) const;
         // True if the current value table maps everything to zero.

      bool can_exist( ) const;
         // True if functions are possible.

      value operator( ) ( const std::vector< value > & args ) const;

      void print( std::ostream& out ) const; 

      function& operator ++ ( );
   };

} 

#endif

