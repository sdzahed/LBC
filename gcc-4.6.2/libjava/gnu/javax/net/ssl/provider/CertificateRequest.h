
// DO NOT EDIT THIS FILE - it is machine generated -*- c++ -*-

#ifndef __gnu_javax_net_ssl_provider_CertificateRequest__
#define __gnu_javax_net_ssl_provider_CertificateRequest__

#pragma interface

#include <java/lang/Object.h>
extern "Java"
{
  namespace gnu
  {
    namespace javax
    {
      namespace net
      {
        namespace ssl
        {
          namespace provider
          {
              class CertificateRequest;
              class ClientCertificateTypeList;
              class X500PrincipalList;
          }
        }
      }
    }
  }
  namespace java
  {
    namespace nio
    {
        class ByteBuffer;
    }
  }
}

class gnu::javax::net::ssl::provider::CertificateRequest : public ::java::lang::Object
{

public:
  CertificateRequest(::java::nio::ByteBuffer *);
  virtual jint length();
  virtual ::gnu::javax::net::ssl::provider::ClientCertificateTypeList * types();
  virtual ::gnu::javax::net::ssl::provider::X500PrincipalList * authorities();
  virtual ::java::lang::String * toString();
  virtual ::java::lang::String * toString(::java::lang::String *);
public: // actually protected
  ::java::nio::ByteBuffer * __attribute__((aligned(__alignof__( ::java::lang::Object)))) buffer;
public:
  static ::java::lang::Class class$;
};

#endif // __gnu_javax_net_ssl_provider_CertificateRequest__
