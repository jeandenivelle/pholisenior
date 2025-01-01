
#ifndef RESO_NAMEGENERATOR_
#define RESO_NAMEGENERATOR_

#include <iostream>
#include <string>

namespace reso
{
   // Intended for the introduction of Skolem functions, or
   // subformula definitions 

   class namegenerator
   {
      std::string base;
      std::string index; 

   public:
      namegenerator( const std::string& base, 
                     const std::string& index = "0000" )
         : base( base ), index( index )
      { }

      std::string next( );
         // Return a string, and increase the counter after that.

      void print( std::ostream& out ) const;
   };
} 

#endif

