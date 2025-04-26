
#include "primtype.h"

namespace semantics
{

   struct value
   {
      primtype tp; 
      unsigned int index; 
         // In case of T, we use
         // 0 = false
         // 1 = true
         // 2 = error

      value( primtype tp, unsigned int index )
         : tp( tp ), index( index )
      { }

      void print( std::ostream& out ) const; 
       
   };

   inline bool operator == ( value val1, value val2 )
   {
      return val1. tp == val2. tp && val1. index == val2. index;
   }

   inline bool operator != ( value val1, value val2 )
   {
      return val1. tp != val2. tp || val1. index != val2. index;
   }

   inline bool preceq( value val1, value val2 )
   {
      if( val1. tp == prim_truthval )
      {
         if( val1. index == 0 || val1. index == 1 )
            return val1 == val2;
      }
      return true;
   }

   inline std::ostream& operator << ( std::ostream& out, value val )
   {
      val. print( out ); 
      return out;
   }
  
    
}

