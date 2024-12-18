
#ifndef RESO_NAMEGENERATOR_
#define RESO_NAMEGENERATOR_

#include <iostream>
#include <string>
#include <unordered_map>

namespace reso
{
   // Intended for the introduction of Skolem functions, or
   // subformula definitions 

   struct namegenerator
   {
      std::unordered_map< std::string, std::string > bases;
         // Maps known bases to the current next index.
         // Instead of using numbers and converting those to strings, 
         // we count directly with strings.

      namegenerator( ) noexcept = default;

      std::string create( const std::string& base );
         // Get the next name for the given base,
         // and increase its index after that.
         // It may be still necessary to check that the name is
         // not used somewhere else.
 
      void print( std::ostream& out ) const;
         // Print current state. 

   };
} 

#endif

