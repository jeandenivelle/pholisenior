
#ifndef SEMANTICS_PRIMTYPE_
#define SEMANTICS_PRIMTYPE_

#include <iostream>

namespace semantics 
{ 
   enum primtype {
      prim_truthval,
      prim_obj  
   };

   inline const char* getcstring( primtype tp )
   {
      switch( tp )
      {
         case prim_truthval: return "Truthval";
         case prim_obj:      return "Obj";
         default:            return "???";
      }
   }

   inline std::ostream& operator << ( std::ostream& os, primtype tp ) 
      { os << getcstring( tp ); return os; }

}

#endif

