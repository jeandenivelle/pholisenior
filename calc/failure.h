
// Written by Hans de Nivelle, July 2025.

#ifndef CALC_FAILURE_
#define CALC_FAILURE_

#include <iostream>

namespace calc
{

   struct failure
   {
      failure( ) noexcept = default;

      void print( std::ostream& out ) const
      {
         out << "(failure)";
      }
   };

}

#endif

