/**
 * Header file for monitors.
 *
 */

#include <algorithm>
#include <functional>
#include <iostream>
#include <string>
#include <vector>

using namespace std;

/**
 * A monitor is either
 */
enum MonitorState {
  // FINE - no errors occured
  FINE = 1,

  // UNKOWN - unknown inputs occured
  UNKNOWN = 0,

  // ERROR - violated output
  ERROR = -1,
};

/**
 * Monitor flags
 */
/*enum MonitorFlags {
  //!
  None = 0,

  //!
  DYNAMIC = 1,

  //!
  RESETABLE = 2,
};*/

// Special states
const int ERROR_STATE = -1;
const int LIGHTNING_STATE = -2;
const int FINAL_STATE = -3;
const int INVALID_STATE = -3;

template <typename T>
struct gvar {
  bool isBound;
  T value;
};

template <typename io_t>
class IMonitor {
 private:
  MonitorState _state;
  //MonitorFlags _flags;

 public:
  virtual ~IMonitor() {}
  virtual void reset() = 0;
  virtual void next(const io_t &input) = 0;

  MonitorState state() const { return _state; }
  void state(MonitorState s) { _state = s; }

  //MonitorFlags flag() const { return _flags; }
  //void flag(MonitorFlags f) { _flags = f; }
  //bool is(MonitorFlags f) { return _flags & f; }
};

template <typename io_t>
class CombinedMonitor : public IMonitor<io_t> {
 public:
  CombinedMonitor() : monitors() { reset(); }

  virtual ~CombinedMonitor() {}

  virtual void next(const io_t &input) override {
    before(input);
    this->state(MonitorState::UNKNOWN);
    eval(input);
    this->state(aggregate());
    cleanup();
  }

  virtual void before(const io_t &input) {}
  virtual void eval(const io_t &input) {}
  virtual MonitorState aggregate() const = 0;
  virtual void cleanup() = 0;

  /*void combine(MonitorState res) {
    if (res == MonitorState::ERROR)
      this->state(MonitorState::ERROR);
    else if (this->state() != MonitorState::ERROR && res == MonitorState::FINE)
      this->state(MonitorState::FINE);
  }*/

  friend CombinedMonitor &operator<<(CombinedMonitor &self,
                                     IMonitor<io_t> *monitor) {
    self.monitors.push_back(monitor);
    return self;
  }
};

// region monitor aggregation
template <typename io_t>
class CombinedAndMonitor : public CombinedMonitor<io_t> {
  virtual MonitorState aggregate() const override { return FINE; };
};

template <typename io_t>
class CombinedOrMonitor : public CombinedMonitor<io_t> {
  virtual MonitorState aggregate() const override { return FINE; };
};
// endregion


template <typename T, int size>
class sregister {
public:
    explicit sregister() :
        buf(new T[size]) {}

    ~sregister() { delete buf; }

    void push(const T item) {
      current = (current+1) % size;
      T[current] = item;
    }

    T get(int pos) const {
      auto pos = (current + pos) % size;
      if(pos<0) pos += size();
      return T[pos];
    }

    //size_t size() const {return size;}

    T operator[](int pos) const { return get(pos); }
private:
    T* buf;
    size_t current = 0;
};
