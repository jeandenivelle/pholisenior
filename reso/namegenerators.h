
#ifndef RESO_NAMEGENERATORS_
#define RESO_NAMEGENERATORS_

#include <iostream>
#include "namegenerator.h"

namespace reso
{
   struct namegenerators
   {
      namegenerator pred = namegenerator( "pred" );
      namegenerator predisprop = namegenerator( "predisprop" );
      namegenerator preddef = namegenerator( "preddef" );
   };

   inline 
   std::ostream& operator << ( std::ostream& out, const namegenerators& gen )
   {
      out << "pred = " << gen. pred << "\n";
      out << "predprop = " << gen. predisprop << "\n";
      out << "preddef = " << gen. preddef << "\n";
      return out;
   }
}

#endif

