#include "function.h"

semantics::function::function( const std::vector< sized_type > & argtypes, 
                               sized_type restype )
   : argtypes( argtypes ),
     restype( restype ),
     values( std::vector< unsigned int > ( domain_size( ))) 
{ }

semantics::function::function( std::vector< sized_type > && argtypes, 
                               sized_type restype )  
   : argtypes( std::move( argtypes )),
     restype( restype ),
     values( std::vector< unsigned int > ( domain_size( ))) 
{ }

semantics::function::function( const std::vector< sized_type > & argtypes,
                               sized_type restype,
                               std::initializer_list< unsigned int > init )
   : argtypes( std::move( argtypes )),
     restype( restype ),
     values( std::vector< unsigned int > ( domain_size( )))
{ 
   if( values. size( ) != init. size( ))
   {
      std::cout << "it must be " << values. size( ) << "\n";
      throw std::logic_error( "size of init table is wrong" );
   }

   values = init;
}

size_t semantics::function::domain_size( ) const
{
   size_t s = 1;
   for( const auto& tp : argtypes )
   {
      if( tp. first == prim_truthval && ( tp. second != 2 && tp. second != 3 )) 
         throw std::logic_error( "truthval must have either 2 or 3 instances" );

      s *= tp. second; 
   }
   return s;
}

bool semantics::function::allzeroes( ) const
{
   for( auto v : values ) 
   {
      if(v) 
         return false;
   }
   return true;
}

bool semantics::function::can_exist( ) const
{
   // Hope it's correct:

   if( restype. second )
      return true;
   else
      return values. empty( ); 
}

semantics::value
semantics::function::operator( ) ( const std::vector< value > & args ) const
{
   if( argtypes. size( ) != args. size( ))
      throw std::logic_error( "number of arguments does not fit to type" );

   size_t factor = 1;
   size_t index = 0;
      // Position from we will take the value.

   for( auto a = args. size( ); a; ) 
   {
      -- a; 
      index += args[a].index * factor;
      factor *= argtypes[a].second;  
   }
   // std::cout << "index = " << index << "\n";
   return value( restype. first, values. at( index ));
}

semantics::function&
semantics::function::operator ++ ( )
{
   auto i = values. size( ); 
   while(i){
      --i;
      values[i]++; 
      if (values[i] < restype. second){
         return *this;
      } 
      values[i] = 0; 
   
   }
   return *this;
}

void 
semantics::function::print( std::ostream& out ) const
{
   out << "function "; 
   for( size_t i = 0; i != argtypes. size( ); ++ i )
   {
      if(i) out << ", ";
      out << argtypes[i]. first << '/' << argtypes[i]. second;
   }
   out << " --> " << restype. first << '/' << restype. second << ":\n";

   for( size_t i = 0; i != values.size( ); ++ i )
   {
      size_t index = i;
      out << "   [";

      for( size_t j = 0; j < argtypes.size(); ++j )
      {
         size_t divisor = 1;
         // compute the total product of all sizes from j+1 to end

         for (size_t k = j + 1; k < argtypes.size(); ++k)
         {
            divisor *= argtypes[k].second;
         }

         unsigned int v = (index / divisor) % argtypes[j].second;
         if(j) out << ", ";
         out << value( argtypes[j]. first, v );
      }
      out << "]: ";
      std::cout << value( restype. first, values[i] ) << "\n";
   }
}

