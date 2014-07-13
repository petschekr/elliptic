var assert = require('assert');
var bn = require('bn.js');
var elliptic = require('../../elliptic');
var utils = elliptic.utils;

var KeyPair = require('./key');
var Signature = require('./signature');

// Node.js dependent
var crypto = require("crypto");
var assert = require("assert");

function EC(options) {
  if (!(this instanceof EC))
    return new EC(options);

  // Shortcut `elliptic.ec(curve-name)`
  if (typeof options === 'string')
    options = elliptic.curves[options];

  // Shortcut for `elliptic.ec(elliptic.curves.curveName)`
  if (options instanceof elliptic.curves.PresetCurve)
    options = { curve: options };

  this.curve = options.curve.curve;
  this.n = this.curve.n;
  this.nh = this.n.shrn(1);
  this.g = this.curve.g;

  // Point on curve
  this.g = options.curve.g;
  this.g.precompute(options.curve.n.bitLength() + 1);

  // Hash for function for DRBG
  this.hash = options.hash || options.curve.hash;
}
module.exports = EC;

EC.prototype.keyPair = function keyPair(priv, pub) {
  return new KeyPair(this, priv, pub);
};

EC.prototype.genKeyPair = function genKeyPair(options) {
  if (!options)
    options = {};

  var bytes = this.n.byteLength();
  var ns2 = this.n.sub(new bn(2));
  do {
    var priv = new bn(crypto.randomBytes(bytes).toString("hex"));
    if (priv.cmp(ns2) > 0)
      continue;

    priv.iaddn(1);
    return this.keyPair(priv);
  } while (true);
};

EC.prototype._truncateToN = function truncateToN(msg, truncOnly) {
  var delta = msg.byteLength() * 8 - this.n.bitLength();
  if (delta > 0)
    msg = msg.shrn(delta);
  if (!truncOnly && msg.cmp(this.n) >= 0)
    return msg.sub(this.n);
  else
    return msg;
};

EC.prototype.sign = function sign(msg, key, options) {
  key = this.keyPair(key, 'hex');
  msg = this._truncateToN(new bn(msg, 16));
  if (!options)
    options = {};

  // Zero-extend key to provide enough entropy
  var bytes = this.n.byteLength();
  var bkey = key.getPrivate().toArray();
  for (var i = bkey.length; i < 21; i++)
    bkey.unshift(0);

  // Zero-extend nonce to have the same byte size as N
  var nonce = msg.toArray();
  for (var i = nonce.length; i < bytes; i++)
    nonce.unshift(0);

  // Number of bytes to generate
  var ns1 = this.n.sub(new bn(1));
  do {
    var k = new bn(crypto.randomBytes(this.n.byteLength()).toString("hex"));
    k = this._truncateToN(k, true);
    if (k.cmpn(1) <= 0 || k.cmp(ns1) >= 0)
      continue;

    var kp = this.g.mul(k);
    if (kp.isInfinity())
      continue;

    var r = kp.getX().mod(this.n);
    if (r.cmpn(0) === 0)
      continue;

    var s = k.invm(this.n).mul(r.mul(key.getPrivate()).iadd(msg)).mod(this.n);
    if (s.cmpn(0) === 0)
      continue;

    // Use complement of `s`, if it is > `n / 2`
    if (options.canonical && s.cmp(this.nh) > 0)
      s = this.n.sub(s);

    return new Signature(r, s);
  } while (true);
};

EC.prototype.verify = function verify(msg, signature, key) {
  msg = this._truncateToN(new bn(msg, 16));
  key = this.keyPair(key, 'hex');
  signature = new Signature(signature, 'hex');

  // Perform primitive values validation
  var r = signature.r;
  var s = signature.s;
  if (r.cmpn(1) < 0 || r.cmp(this.n) >= 0)
    return false;
  if (s.cmpn(1) < 0 || s.cmp(this.n) >= 0)
    return false;

  // Validate signature
  var sinv = s.invm(this.n);
  var u1 = sinv.mul(msg).mod(this.n);
  var u2 = sinv.mul(r).mod(this.n);

  var p = this.g.mulAdd(u1, key.getPublic(), u2);
  if (p.isInfinity())
    return false;

  return p.getX().mod(this.n).cmp(r) === 0;
};

/**
  * Recover a public key from a signature.
  *
  * See SEC 1: Elliptic Curve Cryptography, section 4.1.6, "Public Key Recovery Operation".
  *
  * http://www.secg.org/download/aid-780/sec1-v2.pdf
  */
EC.prototype.recoverPublicKey = function recoverPublicKey(msg, signature, i) {
  assert.strictEqual(i & 3, i, "The recovery param is more than two bits");

  msg = this._truncateToN(new bn(msg, 16));
  signature = new Signature(signature, "hex");
  var r = signature.r;
  var s = signature.s;
  // A set LSB signifies that the y-coordinate is odd
  // By reduction, the y-coordinate is even if it is clear
  var isYOdd = i & 1;
  // The more significant bit specifies whether we should use the
  // first or second candidate key.
  var isSecondKey = i >> 1;

  var n = this.curve.n;
  var G = this.g;
  var p = this.curve.p;

  var pOverFour = p.add(new bn(1)).shrn(2);

  var x = isSecondKey ? r.add(n) : r;
  var R = this.curve.pointFromX(isYOdd, x);
  assert(R.validate(), "Invalid point");
  
  var eNeg = msg.neg().mod(n);
  var rInv = r.invm(n);

  var Q = R.mulAdd(s, G, eNeg).mul(rInv);

  var recoveredKeyPair = this.keyPair();
  recoveredKeyPair._importPublic(Q);
  assert(recoveredKeyPair.validate(), "Invalid public key");
  
  return recoveredKeyPair
}