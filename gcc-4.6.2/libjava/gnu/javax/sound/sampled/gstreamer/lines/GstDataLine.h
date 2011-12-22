
// DO NOT EDIT THIS FILE - it is machine generated -*- c++ -*-

#ifndef __gnu_javax_sound_sampled_gstreamer_lines_GstDataLine__
#define __gnu_javax_sound_sampled_gstreamer_lines_GstDataLine__

#pragma interface

#include <java/lang/Object.h>
#include <gcj/array.h>

extern "Java"
{
  namespace gnu
  {
    namespace javax
    {
      namespace sound
      {
        namespace sampled
        {
          namespace gstreamer
          {
            namespace lines
            {
                class GstDataLine;
            }
          }
        }
      }
    }
  }
  namespace javax
  {
    namespace sound
    {
      namespace sampled
      {
          class AudioFormat;
          class Control;
          class Control$Type;
          class Line$Info;
          class LineListener;
      }
    }
  }
}

class gnu::javax::sound::sampled::gstreamer::lines::GstDataLine : public ::java::lang::Object
{

public:
  GstDataLine(::javax::sound::sampled::AudioFormat *);
  GstDataLine(::javax::sound::sampled::AudioFormat *, jint);
  virtual jint getBufferSize();
  virtual ::javax::sound::sampled::AudioFormat * getFormat();
  virtual jfloat getLevel();
  virtual void addLineListener(::javax::sound::sampled::LineListener *);
  virtual ::javax::sound::sampled::Control * getControl(::javax::sound::sampled::Control$Type *);
  virtual JArray< ::javax::sound::sampled::Control * > * getControls();
  virtual ::javax::sound::sampled::Line$Info * getLineInfo();
  virtual jboolean isControlSupported(::javax::sound::sampled::Control$Type *);
  virtual jboolean isOpen();
  virtual void removeLineListener(::javax::sound::sampled::LineListener *);
public: // actually protected
  virtual void setOpen(::java::lang::Boolean *);
  virtual void setBufferSize(jint);
  virtual void setFormat(::javax::sound::sampled::AudioFormat *);
public:
  virtual jint available() = 0;
  virtual void drain() = 0;
  virtual void flush() = 0;
  virtual jint getFramePosition() = 0;
  virtual jlong getLongFramePosition() = 0;
  virtual jlong getMicrosecondPosition() = 0;
  virtual jboolean isActive() = 0;
  virtual jboolean isRunning() = 0;
  virtual void start() = 0;
  virtual void stop() = 0;
  virtual void close() = 0;
  virtual void open() = 0;
  static const jint DEFAULT_BUFFER_SIZE = 1024;
public: // actually protected
  ::java::lang::Boolean * __attribute__((aligned(__alignof__( ::java::lang::Object)))) open;
private:
  ::javax::sound::sampled::AudioFormat * format;
  jint bufferSize;
public:
  static ::java::lang::Class class$;
};

#endif // __gnu_javax_sound_sampled_gstreamer_lines_GstDataLine__
