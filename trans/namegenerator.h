
#ifndef TRANS_NAMEGENERATOR_
#define TRANS_NAMEGENERATOR_

#include <iostream>
#include <string>
#include <unordered_map>

namespace trans
{
   // Intended for the introduction of Skolem functions or
   // subformula definitions. 

   class namegenerator
   {
      std::unordered_map< std::string, std::string > names;

   public:
      namegenerator( ) noexcept = default;
      namegenerator( namegenerator&& ) = default;
      namegenerator& operator = ( namegenerator&& ) = default;

      std::string get( std::string base );

      void print( std::ostream& out ) const;
   };
} 

#endif

