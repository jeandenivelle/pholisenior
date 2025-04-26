
#include "value.h"

void semantics::value::print( std::ostream& out ) const
{
   if( tp == prim_truthval )
   {
      switch( index )
      {
      case 0: 
         out << "ff"; return;
      case 1:
         out << "tt"; return;
      case 2:
         out << "ee"; return;
      default:
         out << "???"; return;
      }
   }
   
   if( tp == prim_obj )
   {
      out << "obj" << index;
      return; 
   }

   throw std::logic_error( "unknown value type" ); 
}

