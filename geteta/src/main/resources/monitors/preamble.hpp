/**
 * Header file for monitors.
 *
 */

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

  // REMOVABLE -
  REMOVABLE = -2
};

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

 public:
  virtual ~IMonitor() {}
  virtual void reset() = 0;
  virtual void next(const io_t &&input) = 0;

  MonitorState state() { return _state; }
  void state(MonitorState s) { _state = s; }
};

template <typename io_t>
class BaseMonitor : public IMonitor<io_t> {
 protected:
  struct Token {
    int state;
    gv_t globalVars;
  };

  vector<Token> tokens;

  int numErrors;

 public:
  Monitor() : tokens(), numErrors(0), state(MonitorState::FINE) {}

  virtual void reset() {
    state(MonitorState::FINE);
    numErrors = 0;
    tokens.clear();
  }

  void next(const io_t &&input) override {
    vector<Token> newTokens;
    for (auto &&tok : tokens) evaluate(newTokens, tok, input);

    tokens.clear();

    bool hitError = false, hitState = false;
    for (auto &&i : newTokens) {
      switch (i.state) {
        case ERROR_STATE:
          hitError = true;
          break;
        case LIGHTNING_STATE:
          break;
        default: {
          hitState = true;
          tokens.push_back(i);
        }
      }
    }

    state(hitError ? MonitorState::ERROR;
                   : hitState ? MonitorState::FINE : MonitorState::UNKNOWN);
  }

  virtual void evaluate(vector<Token> &newTokens, Token &token,
                        const io_t &input) = 0;
};

template <typename io_t>
class CombinedMonitor : IMonitor<io_t> {
 public:
  CombinedMonitor() : monitors() {}
  virtual ~CombinedMonitor() {}
  void reset() override {
    for (auto &&m : monitors) m.reset();
  }

  virtual void before(const io_t &&input) {}
  virtual void eval(const io_t &&input) {}
  virtual void after() {}

  void combine(MonitorState res) {
      if (res == MonitorState::ERROR) state(MonitorState::ERROR);
      else if (state() != MonitorState::ERROR && res == MonitorState::FINE)
          state(MonitorState::FINE);
  }

  MonitorState next(const io_t &&input) override {
    before(input);
    state(MonitorState::UNKNOWN);
    eval();
    after();
  }
};