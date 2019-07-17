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
 public:
  virtual ~IMonitor() {}
  virtual void reset() = 0;
  virtual MonitorState next(const io_t &&input) = 0;
};

template <typename gv_t, typename io_t>
class Monitor : public IMonitor<io_t> {
 protected:
  struct Token {
    int state;
    gv_t globalVars;
  };

  vector<Token> tokens;

 public:
  Monitor() : tokens(), numErrors(0) {}

  int numErrors;

  virtual void reset() {
    std::cout << "reset monitor\n";
    numErrors = 0;
    tokens.clear();
  }

  MonitorState next(const io_t &&input) {
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

    if (hitError) return MonitorState::ERROR;
    if (hitState) return MonitorState::FINE;
    return MonitorState::UNKNOWN;
  }

  virtual void evaluate(vector<Token> &newTokens, Token &token,
                        const io_t &input) = 0;
};

template <typename io_t>
class CombinedMonitor : IMonitor<io_t> {
  vector<IMonitor<io_t>> monitors;

  typealias Trigger = function<bool(io_t)>;
  typealias MonitorInit = function<Monitor<io_t>(void)>;
  vector<pair<Trigger, MonitorInit>> tokens;

 public:
  CombinedMonitor() : monitors() {}
  virtual ~CombinedMonitor() {}
  void reset() override {
    for (auto &&m : monitors) m.reset();
  }

  MonitorState next(const io_t &&input) override {
    MonitorState combined = MonitorState::UNKNOWN;
    for (auto &&m : monitors) {
      auto res = m.next(input);
      if (res == MonitorState::ERROR)
        combined = MonitorState::ERROR;
      else if (combined != MonitorState::ERROR && res == MonitorState::FINE)
        combined = MonitorState::FINE;
    }
    return combined;
  }
};