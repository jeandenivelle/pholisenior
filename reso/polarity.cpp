
#include "polarity.h"

const char* reso::getcstring( polarity pol )
{
   switch( pol )
   {
   case pol_pos:       return "pos"; 
   case pol_neg:       return "neg";
   case pol_prop:      return "prop";
   case pol_negprop:   return "neg-prop";
   default:            return "???";
   }
}

reso::polarity reso::negate( reso::polarity pol )
{
   switch( pol )
   {
   case pol_pos:       return pol_neg;
   case pol_neg:       return pol_pos;
   case pol_prop:      return pol_negprop;
   case pol_negprop:   return pol_prop;
   }
   std::cout << pol << "\n";
   throw std::logic_error( "cannot negate" ); 
}

logic::selector reso::demorgan( logic::selector sel, polarity pol )
{
   if( pol == pol_pos || pol == pol_prop )
   {
      // We still check:

      switch( sel )
      {
      case logic::op_kleene_and:
      case logic::op_kleene_or:
      case logic::op_kleene_forall:
      case logic::op_kleene_exists:
         return sel;
      }

   }
   else
   {
      switch( sel )
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

   std::cout << "demorgan " << sel << " / " << pol << "\n";
   throw std::runtime_error( "De Morgan: unhandled case" ); 
}





