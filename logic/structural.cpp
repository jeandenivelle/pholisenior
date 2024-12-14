
#include "structural.h"
#include "pretty.h"
#include "kbo.h"

#if 0
namespace
{
   // We don't want to type this all the time:

   bool equal( const logic::type& tp1, const logic::type& tp2 )
   {
      return is_eq( logic::kbo::topleftright( tp1, tp2 ));
   }
}
#endif


void logic::checkstructure( beliefstate& everything, errorstack& err )
{
#if 0
   for( auto& onename : everything )
   {
      {
         size_t nrstructs = 0; 
 
         for( size_t i = 0; i != onename. second. size( ); ++ i )
         {
            if( onename. second[i]. sel( ) == bel_struct )
               ++ nrstructs;
         }

         if( nrstructs > 1 )
         {
            throw std::runtime_error( "more than one struct def" );
               // Create a nice error message when it happens.
         }
      }

      for( size_t i = 0; i != onename. second. size( ); ++ i )
      {
         exactname fullname = exactname( onename. first, i );

         switch( onename. second[i]. sel( ))
         {

         case bel_struct:
            {
               const auto& str = onename.second[i]. view_struct( ). def( );;
               for( const auto& fld : str )
               {
                  metastructchecker meta( everything, rk, fullname, fld. tp );

                  auto dontcare = meta. check( );
                  if( !meta. good( ))
                  {
                     for( const auto& err : meta. errors )
                     {
                        errors. extend( );
                        errors. last( ) << "checking field " << fld.name;
                        errors. last( ) << " of " << fullname << " : ";
                        errors. last( ) << err;
                     }
                  }
               } 
 
               break;
            }

         case bel_decl:
            {
               auto decl = onename.second[i]. view_decl( );
               metastructchecker meta( everything, rk, fullname, decl. tp( ));

               auto dontcare = meta. check( );
               if( !meta. good( ))
               {
                  errors. extend( );
                  errors. last( ) << "in declaration " << fullname << " ";  
                  errors. last( ) << "the type is not well formed ";
                  errors. last( ) << decl. tp( ); 
               }

               break; 
            }  

         case bel_def:
            {
               auto def = onename.second[i]. view_def( );
              
               structchecker chk( everything, rk, fullname, 
                                  def. extr_val( ));  
               auto bodytype = chk. check( );
               def. update_val( chk. goal );
              
               if( !chk. good( ))
               {
                  for( const auto& err : chk. errors ) 
                  {
                     errors. extend( );
                     errors. last( ) << "while checking the definition of ";
                     errors. last( ) << fullname << " : at " << err. first << " " << err. second;
                  }
               }
               else
               {
                  if( !equal( bodytype. value( ), def. tp( )) )
                  {
                     std::cout << bodytype. value( ) << "\n";
                     std::cout << onename.second[i] << "\n";
                     errors. extend( );
                     errors. last( ) << "in definition " << fullname << " ";
                     errors. last( ) << "the true type is "
                                     << bodytype. value( ) << ", ";
                     errors. last( ) << "while the declared type is " 
                                     << def. tp( );  
                  }
               }               
               break;
            } 

         case bel_thm:
            {
               auto thm = onename.second[i]. view_thm( );
               structchecker chk( everything, rk, fullname, thm. extr_form( ));
               chk. check( );
               thm. update_form( chk. goal ); 

               if( !chk. good( ))
               {
                  for( const auto& err : chk. errors )
                  {
                     errors. extend( );
                     errors. last( ) << "while checking theorem ";
                     errors. last( ) << fullname << " : at " << err. first << " " << err. second;
                  }
               }
               break;
            }

         case bel_fld:
            {
               auto fld = onename.second[i]. view_field( ); 

               auto p = everything. find( fld. parent( ));
               if( p == everything. end( ))
                  throw std::runtime_error( "type not found" );

               size_t def = 0;
               size_t nrtypes = 0;
               for( size_t i = 0; i != p -> second. size( ); ++ i )
               {
                  if( p -> second[i]. sel( ) == bel_struct )
                  {
                     ++ nrtypes;
                     def = i;
                  }
               }

               if( nrtypes != 1 )
                   throw std::runtime_error( "problem with type definition" );

               const auto& sdef = p -> second[ def ]. view_struct( ). def( );

               if( fld. offset( ) >= sdef. size( ))
               {
                  throw std::runtime_error( "struct out of range" );
               }
 
               if( !equal( sdef. at( fld. offset( ) ). tp, fld. tp( )) )
               {
                  throw std::runtime_error( "struct types differ" );
               }
 
               rk. setbelow( fullname, exactname( fld. parent( ), def ));

               break;
            }

         default:
            std::cout << "checkstructure not implemented for ";
            std::cout << onename. second[i]. sel( ) << "\n";
            throw std::runtime_error( "quitting" );
         }
      }

   }
   return errors; 
#endif
}


namespace
{
   // Returns true if blfs contains a field function for field
   // fld/offset of struct structname. 

#if 0
   bool isthere( const logic::beliefstate& blfs,
                 const logic::fielddef fld, size_t offset, 
                 normident structname )
   {
      // std::cout << "checking presence of field ";
      // std::cout << fld << "/" << offset << " " << structname << "\n";

      auto p = blfs. find( fld. name );

      if( p == blfs. end( ))
         return false;

      for( const auto& b : p -> second )
      {
         if( b. sel( ) == logic::bel_fld )
         {
            auto f = b. view_field( ); 
            if( equal( f. tp( ), fld. tp ) &&
                f. parent( ) == structname &&
                f. offset( ) == offset )
            {
               return true; 
            } 
         }
      }
      return false;
   }
#endif
}


#if 0

logic::correctness
logic::checkproofterm( std::ostream& out, const beliefstate& state, 
                       const term& proof, size_t cutoff )
{
   correctness corr;

   checker check( &state, cutoff, proof );

   context ctxt;
   position pos;
   try
   {
      const auto& tp = check. typecheck( ctxt, pos, proof );

      if( tp. sel( ) != sel_func || 
          tp. view_func( ). result( ). sel( ) != sel_contr || 
          tp. view_func( ). size( ) != 1 ||
          tp. view_func( ). arg(0). sel( ) != sel_belief ) 
      {
         uniquenamestack names;
         pretty::print( out, names,
            error( err_typediff, 
                   type( sel_func, type( sel_contr ), { type( sel_belief ) } ), tp, 
                   "proof term has wrong type" ));

         ++ corr. type_errors; 
      }
   }
   catch( const failure& f )
   {
      ctxt. restore(0);
      check. print_errors( out, ctxt );
      corr. type_errors += check. nr_errors( ); 
   }

   corr. unfinisheds += check. nr_unfinished( ); 
   return corr; 
}

#endif


bool 
logic::checkandresolve( const beliefstate& blfs, errorstack& errors,
                        type& tp ) 
{
   if constexpr( false )
   {
      std::cout << "checkandresolve ";
      pretty::print( std::cout, blfs, tp, {0,0} );
      std::cout << "\n";
   }
 
   switch( tp. sel( ))
   {
   case type_truthval:
   case type_obj:
      return true;
 
   case type_unchecked:
      {
         auto id = tp. view_unchecked( );
         auto& defs = blfs. getstructdefs( id. id( ));

         if( defs. size( ) == 0 ) 
         {
            errorstack::builder bld;

            bld << "identifier used as type has no struct-def: ";
            bld << id. id( ); 
            errors. push( std::move( bld ));

            return false;
         }

         if( defs. size( ) > 1 )
         {
            errorstack::builder bld;

            bld << "identifier used as type has " << defs. size( );
            bld << " struct-defs: ";
            bld << id. id( ); 
            errors. push( std::move( bld ));

            return false;
         }

         tp = type( type_struct, defs[0] );
         return true;
      }

   case type_func:
      {
         bool correct = true; 

         auto func = tp. view_func( );
         {
            type res = func. extr_result( );
            if( !checkandresolve( blfs, errors, res ))
               correct = false;

            func. update_result( res );
         }
           
         for( size_t i = 0; i != func. size( ); ++ i )
         {
            type arg = func. extr_arg(i);
            if( !checkandresolve( blfs, errors, arg ))
               correct = false;

            func. update_arg( i, arg );
         }
         return correct;
      }
   } 
   std::cout << "checkandresolve: " << tp. sel( ) << "\n";
   throw std::runtime_error( "not implemented for this case" );
}


namespace logic
{
   namespace
   {
      errorstack::builder errorheader( const beliefstate& blfs,
                                       context& ctxt, 
                                       const term& t )
      {
         errorstack::builder res;
         res << "\n";
         res << "----------------------------------------------------\n";
         auto un = pretty::print( res, blfs, ctxt );
         res << "Term:\n   ";
         pretty::print( res, blfs, un, t, {0,0} );
         res << "\n";
         return res; 
      }
   }
}


std::optional< logic::type > 
logic::checkandresolve( const beliefstate& blfs, 
                        errorstack& errors, context& ctxt, 
                        term& t ) 
{
   if constexpr( false )
   {
      std::cout << "\n";
      std::cout << "checking type\n";
      auto un = pretty::print( std::cout, blfs, ctxt );
      std::cout << "term:\n   ";
      pretty::print( std::cout, blfs, un, t, {0,0} );
      std::cout << '\n';
   }

   switch ( t. sel( )) 
   {
#if 0
   case op_inexact:
   case op_exact:
      {
         auto id = t. view_ident( ); 
         auto p = blfs. find( id. id( ));
         if( p == blfs. end( ))
         {
            throw std::runtime_error( "not found" ); 
         }
        
         if( t. sel( ) == op_exact )
         {
            if( id. index( ) >= p -> second. size( ))
               throw std::runtime_error( "wrong exact" );
            else
            {
               auto res = try_apply( p -> second[ id. index( ) ], { } ); 
               if( res. has_value( ))
                  std::cout << "won " << res. value( ) << "\n";
               else
                  std::cout << "lost\n"; 
            }
 
         } 
         else
         {
            std::cout << "inexact\n";

         }

         throw std::runtime_error( "not implemented" );
      }

#endif
   case op_debruijn:
      {
         size_t index = t. view_debruijn( ). index( );
         if( index >= ctxt. size( ) ) 
         {
            // This means that the data structure is corrupted.
            // We don't try to pretty print, because it would crash.

            errorstack::builder err;  
            err << "De Bruijn index #" << index << " is out of range\n";
            errors. push( std::move( err ));
            return { }; 
         }
         return ctxt. gettype( index ); 
      }

   case op_false:
   case op_error:
   case op_true:
      return type( type_truthval );

   case op_not:
   case op_prop:
      {
         auto un = t. view_unary( );

         std::optional< type > tp;
         {
            auto sub = un. extr_sub( );
            tp = checkandresolve( blfs, errors, ctxt, sub );
            un. update_sub( sub );
         }

         if( tp. has_value( ) && tp. value( ). sel( ) != type_truthval )
         {
            auto err = errorheader( blfs, ctxt, t );
            err << "argument of logical operator has wrong type ";
            pretty::print( err, blfs, tp. value( ), {0,0} ); 
            errors. push( std::move( err ));
         }

         return type( type_truthval );
      }

   case op_and:
   case op_or:
   case op_implies:
   case op_equiv:
   case op_lazy_and:
   case op_lazy_or:
   case op_lazy_implies:
      {
         auto bin = t. view_binary( );

         std::optional< type > tp1;
         {  
            auto sub1 = bin. extr_sub1( );
            tp1 = checkandresolve( blfs, errors, ctxt, sub1 );
            bin. update_sub1( sub1 );
         }

         std::optional< type > tp2; 
         {
            auto sub2 = bin. extr_sub2( );
            tp2 = checkandresolve( blfs, errors, ctxt, sub2 );
            bin. update_sub2( sub2 );
         }

         if( tp1. has_value( ) && tp1. value( ). sel( ) != type_truthval )
         {
            auto err = errorheader( blfs, ctxt, t );
            err << "first argument of logical operator has wrong type ";
            pretty::print( err, blfs, tp1. value( ), {0,0} ); 
            errors. push( std::move( err ));
         }

         if( tp2. has_value( ) && tp2. value( ). sel( ) != type_truthval )
         {
            auto err = errorheader( blfs, ctxt, t );
            err << "second argument of logical operator has wrong type ";
            pretty::print( err, blfs, tp2. value( ), {0,0} ); 
            errors. push( std::move( err ));
         }

         return type( type_truthval ); 
      }

   case op_equals:
      {
         auto bin = t. view_binary( );

         std::optional< type > tp1;
         {
            auto sub1 = bin. extr_sub1( );
            tp1 = checkandresolve( blfs, errors, ctxt, sub1 );
            bin. update_sub1( sub1 );
         }

         std::optional< type > tp2;
         {
            auto sub2 = bin. extr_sub2( );
            tp2 = checkandresolve( blfs, errors, ctxt, sub2 );
            bin. update_sub2( sub2 );
         }

         if( tp1. has_value( ) && tp1. value( ). sel( ) != type_obj )
         {
            auto err = errorheader( blfs, ctxt, t ); 
            err << "first argument of equality must be O, but is ";
            pretty::print( err, blfs, tp1. value( ), {0,0} );
            err << "\n";
            errors. push( std::move( err ));
         }

         if( tp2. has_value( ) && tp2. value( ). sel( ) != type_obj )
         {
            auto err = errorheader( blfs, ctxt, t );
            err << "second argument of equality must be O, but is ";
            pretty::print( err, blfs, tp2. value( ), {0,0} ); 
            errors. push( std::move( err ));
         }

         return type( type_truthval ); 
      }

   case op_forall:
   case op_exists:
   case op_kleene_forall:
   case op_kleene_exists: 
      {
         auto quant = t. view_quant( );

         size_t contextsize = ctxt. size( );

         size_t errstart = errors. size( );
            // If we produce errors, they start here.

         bool correct = true;

         for( size_t i = 0; i != quant. size( ); ++ i )
         {
            auto vt = quant. extr_var(i);
             
            if( !checkandresolve( blfs, errors, vt. tp ))
               correct = false;

            quant. update_var( i, vartype( vt. pref, vt. tp ));
         }

         if( !correct )
         {
            auto err = errorheader( blfs, ctxt, t );  
            errors. addheader( errstart, std::move( err ));
            return type( type_truthval ); 
         }

         for( size_t i = 0; i != quant. size( ); ++ i )
            ctxt. extend( quant. var(i). pref, quant. var(i). tp );

         std::optional< type > bodytype; 

         {
            auto bod = quant. extr_body( );
            bodytype = checkandresolve( blfs, errors, ctxt, bod ); 
            quant. update_body( bod );
         }

         ctxt. restore( contextsize );

         // If the body has a type, and this type is not T, we need to
         // complain:

         if( bodytype. has_value( ) &&
             bodytype. value( ). sel( ) != type_truthval )
         {
            auto err = errorheader( blfs, ctxt, t );
            err << "body of quantifier does have type T: ";
            pretty::print( err, blfs, bodytype. value( ), {0,0} );
         }

         // Whatever happened, the result is always truthval:

         return type_truthval; 
      }

   case op_apply:
      {
         auto ap = t. view_apply( );
         std::vector< type > argtypes;

         // We first deal with the arguments:

         for( size_t i = 0; i != ap. size( ); ++ i )
         {
            auto arg = ap. extr_arg(i);

            auto tp = checkandresolve( blfs, errors, ctxt, arg );
            if( tp. has_value( ))  
               argtypes. push_back( std::move( tp. value( )) ); 
           
            ap. update_arg( i, arg ); 
         }

         // If some subterms did not have a type, we cannot return a type
         // by ourselves, so we quietly give up. 

         if( argtypes. size( ) < ap. size( ))
            return { };

         // If ap. func( ) is an inexact identifier, we treat this
         // separately, because we cannot simply recurse. 
         // In order to find the correct overload of an identifier, 
         // we need to know the types of the arguments.

         if( ap. func( ). sel( ) == op_unchecked )
         {
            const identifier& ident = ap. func( ). view_unchecked( ). id( );
            std::cout << "ident = " << ident << "\n";

            const auto& overl = blfs. getfunctions( ident );

            if( overl. size( ) == 0 )
            {
               auto err = errorheader( blfs, ctxt, t );
               err << "unknown identifier " << ident << " used as function";
               errors. push( std::move( err ));
               return { };
            }

            std::vector< std::pair< exact, type >> results;
               // These will be the overloads that can be applied
               // with their return types.

            for( const auto& cand : overl )
            {
               auto res = try_apply( blfs, cand, argtypes, 0 );
               if( res. has_value( ))
                  results. push_back( { cand, std::move( res. value( )) } ); 
            } 

            std::cout << "applicable candidates\n";
            for( const auto& cand : results ) 
            {
               std::cout << "   " << cand. first << " --> " 
                         << cand. second << "\n";
            }

            if( results. size( ) == 0 )
            {
               auto err = errorheader( blfs, ctxt, t );
               err << "no applicable overload found for " << ident;
               err << " in application term"; 
               errors. push( std::move( err )); 
               return { };
            }
           
            if( results. size( ) > 1 )
            {
               auto err = errorheader( blfs, ctxt, t );
               err << "cannot resolve " << ident;
               err << " in application term\n"; 
               err << "   candidates are ";
               for( size_t i = 0; i != results. size( ); ++ i )
               {
                  if(i) err << ", ";
                  err << results[i]. first;
               }
               err << "\n";
               errors. push( std::move( err ));
               return { };
            }
 
            ap. update_func( term( op_exact, results. front( ). first )); 
            return results. front( ). second;
         }

         std::optional< type > ftype;
         {
            auto func = ap. extr_func( );
            ftype = checkandresolve( blfs, errors, ctxt, func );
            ap. update_func( func );  
         }

         if( !ftype. has_value( ))
            return ftype;  // Nothing can be done.

         auto res = try_apply( ftype. value( ), argtypes, 0 ); 

         if( res. has_value( ))
            return res;
         else
         { 
            auto err = errorheader( blfs, ctxt, t );
            err << "cannot apply function of type ";
            pretty::print( err, blfs, ftype. value( ), {0,0} ); 
            err << " on argument(s)\n";
            for( size_t i = 0; i != argtypes. size( ); ++ i )
            {
               err << "   "; 
               pretty::print( err, blfs, argtypes[i], {0,0} );
            }
            std::cout << err. str( ) << "\n";
            errors. push( std::move( err ));

            return { };
         }

         throw std::runtime_error( "not implemented" );
      }

   case op_lambda:
      {
         auto lamb = t. view_lambda( );

         bool correct = true;

         size_t errstart = errors. size( );

         for( size_t i = 0; i != lamb. size( ); ++ i ) 
         {
            auto vt = lamb. extr_var(i);
               // We need to extract, because we must resolve overloads.

             if( !checkandresolve( blfs, errors, vt. tp ))
               correct = false;

            lamb. update_var( i, vartype( vt. pref, vt. tp ));
         }

         if( !correct )
         {
            auto err = errorheader( blfs, ctxt, t );  
            errors. addheader( errstart, std::move( err ));
            return { };
         }

         size_t contextsize = ctxt. size( );
         for( size_t i = 0; i != lamb. size( ); ++ i )
            ctxt. extend( lamb. var(i). pref, lamb. var(i). tp );

         std::optional< type > bodytype;

         {
            auto bod = lamb. extr_body( );
            bodytype = checkandresolve( blfs, errors, ctxt, bod );
            lamb. update_body( bod );
         }

         ctxt. restore( contextsize );

         if( bodytype. has_value( ))
         {
            bodytype. value( ) = type( type_func, bodytype. value( ), { } );
            auto func = bodytype. value( ). view_func( );
            for( size_t i = 0; i != lamb. size( ); ++ i )
               func. push_back( lamb. var(i). tp ); 
            return bodytype; 
         }
         else
            return { };
      }
   }
   
   std::cout << "typechecking: selector = " << t. sel( ) << "\n";
   throw std::logic_error( "typechecking: selector not implemented" );
}


#if 0
   if( over. empty( ))
   {
      auto hd = errorheader( blfs, context, 
   }

   const auto& cand = it -> second;
      // This is the vector of overload candidates. There must be
      // exactly one that can be used.
      // We do not have a 'nearest fit' rule like C++ or Java has.

   size_t nrfits = 0;
   size_t lastfit = 0;   // Only meaningful when nrfits > 0.

   std::optional< type > restype;
 
   for( size_t i = 0; i != cand. size( ); ++ i ) 
   {
      std::optional< type > tp = try_apply( cand[i], argtypes );
      if( tp. has_value( ))
      { 
         ++ nrfits; 
         lastfit = i; 
         restype = std::move( tp ); 
      }
   }

   // If id is an exact identifier, it must contain the overload
   // that we would have found if we would have been inexact,
   // otherwise we make it inexact again: 

   if( id. sel( ) == op_exact )
   {
      if( nrfits != 1 || lastfit != id. view_ident( ). index( ))
      {
         add_error( pos,
                error( err_overload, argtypes. begin( ), argtypes. end( ),
                       "wrong exact overload for", ident ));

         id = term( op_inexact, ident, 0 );
         return { }; 
      }
     
      if( !rk. setbelow( exactname( ident, lastfit ), goalname ))
         throw std::runtime_error( "circularity" );

      return restype;  
   }

   // id is not exact :
 
   if( nrfits == 0 ) 
   {
      add_error( pos, 
            error( err_overload, argtypes. begin( ), argtypes. end( ),
      id = term( op_inexact, ident, 0 );
      return { };
   }

   if( nrfits > 1 )
   {
      add_error( pos,
          error( err_overload, argtypes. begin( ), argtypes. end( ),
                 "more than one overload for", ident ));
      return { }; 
   }

   // We make id exact, and mark that it should be below goalname. 

   id = term( op_exact, ident, lastfit );
   if( !rk. setbelow( exactname( ident, lastfit ), goalname ))
      throw std::runtime_error( "circularity" );

   return restype;
#endif



std::optional< logic::type > 
logic::try_apply( type ftype, 
                  const std::vector< type > & argtypes, size_t pos )
{
   if( pos > argtypes. size( ))
      throw std::logic_error( "pos > size( )" );

   std::cout << "trying to apply " << ftype << " on\n";
   for( size_t i = pos; i != argtypes. size( ); ++ i ) 
      std::cout << "   " << i << " : " << argtypes[i] << "\n";
   std::cout << "\n";

   while( pos != argtypes. size( ))
   {
      if( ftype. sel( ) != type_func )
         return { };

      auto fun = ftype. view_func( );

      // args [ pos ... ] must be long enough to contain
      // the required types: 

      if( pos + fun. size( ) > argtypes. size( ))
         return { };  
 
      for( size_t i = 0; i != fun. size( ); ++ i )
      {
         if( !is_eq( kbo::topleftright( fun. arg(i), argtypes[ pos ] )))
         {
            return { };
         }
         ++ pos; 
      }

      ftype = fun. result( ); 
   }

   return ftype; 
}


std::optional< logic::type >
logic::try_apply( const beliefstate& blfs, exact name, 
                  const std::vector< type > & argtypes, size_t pos )
{
   std::cout << "trying to apply belief " << name << " on\n";
   for( size_t i = pos; i != argtypes. size( ); ++ i )
      std::cout << "   " << i << " : " << argtypes[i];
   std::cout << "\n";

   const auto& bel = blfs. at( name ). first;
   switch( bel. sel( )) 
   {
#if 0
      case bel_def: 
         return try_apply( bel. view_def( ). tp( ), argtypes, 0 );

      case bel_decl:
         return try_apply( bel. view_decl( ). tp( ), argtypes, 0 );
#endif
      case bel_fld:
         {
            auto fld = bel. view_field( ); 
            auto parenttype = fld. parenttype( );
           
            if( pos + 1 <= argtypes. size( ) && 
                argtypes[ pos ]. sel( ) == type_struct &&
                argtypes[ pos ]. view_struct( ). def( ) == parenttype )
            {
               const belief& parentblf = blfs. at( parenttype ). first;
                  // The belief in the parent.

               if( parentblf. sel( ) != bel_struct )
                  throw std::runtime_error( "parent type not a structdef" );
        
               const structdef& parentdef = 
                  parentblf. view_struct( ). def( ); 

               return try_apply( parentdef. at( fld. offset( )). tp,
                                 argtypes, pos + 1 );
            }
            return { };
         }  

      case bel_constr:
         {
            const auto& structblf = 
               blfs. at( bel. view_constr( ). tp( )). first;
                  // Belief in the struct that we are trying to construct.

            if( structblf. sel( ) != bel_struct )
               throw std::runtime_error( "constructed type not a structdef" );

            const structdef& sdef =
               structblf. view_struct( ). def( ); 

            std::cout << sdef << "\n";

            if( pos + sdef. size( ) != argtypes. size( ))
               return { };
                  // No currying for constructors.

            for( size_t i = 0; i != sdef. size( ); ++ i )
            {
               if( !is_eq( kbo::topleftright( sdef. at(i). tp, 
                                              argtypes[ pos + i ] )))
               {
                  return { };
               }

               std::cout << "check passed " << sdef. at(i). tp << "\n";
            }
            
            return type( type_struct, bel. view_constr( ). tp( )); 
         }
   }

   throw std::runtime_error( "try_apply, belief is not implemented" );
}

