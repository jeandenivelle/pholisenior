

#include <vector>
#include <iostream>

#include "logic/type.h"

namespace semantics
{

   struct function
   {
      logic::type restype;
      std::vector< logic::type > args;

      std::vector< unsigned int > values;

      
   };
 
};

