
#include "polarity.h"

const char* trans::getcstring( polarity pol )
{
   switch( pol )
   {
   case pol_pos:       return "pos"; 
   case pol_neg:       return "neg";
   default:            return "???";
   }
}

trans::polarity trans::operator - ( polarity pol )
{
   switch( pol )
   {
   case pol_pos:       return pol_neg;
   case pol_neg:       return pol_pos;
   }
   std::cout << pol << "\n";
   throw std::logic_error( "cannot negate" ); 
}


logic::selector trans::demorgan( polarity pol, logic::selector op )
{
   if( pol == pol_pos )
   {
      // We still check:

      switch( op )
      {
      case logic::op_kleene_and:
      case logic::op_kleene_or:
      case logic::op_kleene_forall:
      case logic::op_kleene_exists:
         return op; 
      }
   }
   else
   {
      switch( op )
      {
      case logic::op_kleene_and:
         return logic::op_kleene_or;
 
      case logic::op_kleene_or:
         return logic::op_kleene_and; 

      case logic::op_kleene_forall:
         return logic::op_kleene_exists;

      case logic::op_kleene_exists:
         return logic::op_kleene_forall;
      }
   }

   std::cout << "demorgan " << op << " / " << pol << "\n";
   throw std::runtime_error( "De Morgan: unhandled case" ); 
}





