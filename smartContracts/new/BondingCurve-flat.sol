pragma solidity ^0.5.2;

/**
 * @title ERC20 interface
 * @dev see https://eips.ethereum.org/EIPS/eip-20
 */
interface IERC20 {
    function transfer(address to, uint256 value) external returns (bool);

    function approve(address spender, uint256 value) external returns (bool);

    function transferFrom(address from, address to, uint256 value) external returns (bool);

    function totalSupply() external view returns (uint256);

    function balanceOf(address who) external view returns (uint256);

    function allowance(address owner, address spender) external view returns (uint256);

    event Transfer(address indexed from, address indexed to, uint256 value);

    event Approval(address indexed owner, address indexed spender, uint256 value);
}

/**
 * @title SafeMath
 * @dev Unsigned math operations with safety checks that revert on error
 */
library SafeMath {
    /**
     * @dev Multiplies two unsigned integers, reverts on overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-solidity/pull/522
        if (a == 0) {
            return 0;
        }

        uint256 c = a * b;
        require(c / a == b);

        return c;
    }

    /**
     * @dev Integer division of two unsigned integers truncating the quotient, reverts on division by zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        // Solidity only automatically asserts when dividing by 0
        require(b > 0);
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold

        return c;
    }

    /**
     * @dev Subtracts two unsigned integers, reverts on overflow (i.e. if subtrahend is greater than minuend).
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b <= a);
        uint256 c = a - b;

        return c;
    }

    /**
     * @dev Adds two unsigned integers, reverts on overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a);

        return c;
    }

    /**
     * @dev Divides two unsigned integers and returns the remainder (unsigned integer modulo),
     * reverts when dividing by zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b != 0);
        return a % b;
    }
}

/**
 * @title Standard ERC20 token
 *
 * @dev Implementation of the basic standard token.
 * https://eips.ethereum.org/EIPS/eip-20
 * Originally based on code by FirstBlood:
 * https://github.com/Firstbloodio/token/blob/master/smart_contract/FirstBloodToken.sol
 *
 * This implementation emits additional Approval events, allowing applications to reconstruct the allowance status for
 * all accounts just by listening to said events. Note that this isn't required by the specification, and other
 * compliant implementations may not do it.
 */
contract ERC20 is IERC20 {
    using SafeMath for uint256;

    mapping (address => uint256) internal _balances;

    mapping (address => mapping (address => uint256)) internal _allowed;

    uint256 internal _totalSupply;

    /**
     * @dev Total number of tokens in existence
     */
    function totalSupply() public view returns (uint256) {
        return _totalSupply;
    }

    /**
     * @dev Gets the balance of the specified address.
     * @param owner The address to query the balance of.
     * @return A uint256 representing the amount owned by the passed address.
     */
    function balanceOf(address owner) public view returns (uint256) {
        return _balances[owner];
    }

    /**
     * @dev Function to check the amount of tokens that an owner allowed to a spender.
     * @param owner address The address which owns the funds.
     * @param spender address The address which will spend the funds.
     * @return A uint256 specifying the amount of tokens still available for the spender.
     */
    function allowance(address owner, address spender) public view returns (uint256) {
        return _allowed[owner][spender];
    }

    /**
     * @dev Transfer token to a specified address
     * @param to The address to transfer to.
     * @param value The amount to be transferred.
     */
    function transfer(address to, uint256 value) public returns (bool) {
        _transfer(msg.sender, to, value);
        return true;
    }

    /**
     * @dev Approve the passed address to spend the specified amount of tokens on behalf of msg.sender.
     * Beware that changing an allowance with this method brings the risk that someone may use both the old
     * and the new allowance by unfortunate transaction ordering. One possible solution to mitigate this
     * race condition is to first reduce the spender's allowance to 0 and set the desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     * @param spender The address which will spend the funds.
     * @param value The amount of tokens to be spent.
     */
    function approve(address spender, uint256 value) public returns (bool) {
        _approve(msg.sender, spender, value);
        return true;
    }

    /**
     * @dev Transfer tokens from one address to another.
     * Note that while this function emits an Approval event, this is not required as per the specification,
     * and other compliant implementations may not emit the event.
     * @param from address The address which you want to send tokens from
     * @param to address The address which you want to transfer to
     * @param value uint256 the amount of tokens to be transferred
     */
    function transferFrom(address from, address to, uint256 value) public returns (bool) {
        _transfer(from, to, value);
        _approve(from, msg.sender, _allowed[from][msg.sender].sub(value));
        return true;
    }

    /**
     * @dev Increase the amount of tokens that an owner allowed to a spender.
     * approve should be called when _allowed[msg.sender][spender] == 0. To increment
     * allowed value is better to use this function to avoid 2 calls (and wait until
     * the first transaction is mined)
     * From MonolithDAO Token.sol
     * Emits an Approval event.
     * @param spender The address which will spend the funds.
     * @param addedValue The amount of tokens to increase the allowance by.
     */
    function increaseAllowance(address spender, uint256 addedValue) public returns (bool) {
        _approve(msg.sender, spender, _allowed[msg.sender][spender].add(addedValue));
        return true;
    }

    /**
     * @dev Decrease the amount of tokens that an owner allowed to a spender.
     * approve should be called when _allowed[msg.sender][spender] == 0. To decrement
     * allowed value is better to use this function to avoid 2 calls (and wait until
     * the first transaction is mined)
     * From MonolithDAO Token.sol
     * Emits an Approval event.
     * @param spender The address which will spend the funds.
     * @param subtractedValue The amount of tokens to decrease the allowance by.
     */
    function decreaseAllowance(address spender, uint256 subtractedValue) public returns (bool) {
        _approve(msg.sender, spender, _allowed[msg.sender][spender].sub(subtractedValue));
        return true;
    }

    /**
     * @dev Transfer token for a specified addresses
     * @param from The address to transfer from.
     * @param to The address to transfer to.
     * @param value The amount to be transferred.
     */
    function _transfer(address from, address to, uint256 value) internal {
        require(to != address(0));

        _balances[from] = _balances[from].sub(value);
        _balances[to] = _balances[to].add(value);
        emit Transfer(from, to, value);
    }

    /**
     * @dev Approve an address to spend another addresses' tokens.
     * @param owner The address that owns the tokens.
     * @param spender The address that will spend the tokens.
     * @param value The number of tokens that can be spent.
     */
    function _approve(address owner, address spender, uint256 value) internal {
        require(spender != address(0));
        require(owner != address(0));

        _allowed[owner][spender] = value;
        emit Approval(owner, spender, value);
    }

}

/**
 * @title Ownable
 * @dev The Ownable contract has an owner address, and provides basic authorization control
 * functions, this simplifies the implementation of "user permissions".
 */
contract Ownable {
    address internal _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev The Ownable constructor sets the original `owner` of the contract to the sender
     * account.
     */
    constructor () internal {
        _owner = msg.sender;
        emit OwnershipTransferred(address(0), _owner);
    }

    /**
     * @return the address of the owner.
     */
    function owner() public view returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(isOwner());
        _;
    }

    /**
     * @return true if `msg.sender` is the owner of the contract.
     */
    function isOwner() public view returns (bool) {
        return msg.sender == _owner;
    }

    /**
     * @dev Allows the current owner to relinquish control of the contract.
     * It will not be possible to call the functions with the `onlyOwner`
     * modifier anymore.
     * @notice Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    /**
     * @dev Allows the current owner to transfer control of the contract to a newOwner.
     * @param newOwner The address to transfer ownership to.
     */
    function transferOwnership(address newOwner) public onlyOwner {
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers control of the contract to a newOwner.
     * @param newOwner The address to transfer ownership to.
     */
    function _transferOwnership(address newOwner) internal {
        require(newOwner != address(0));
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}

/**
 * bancor formula by bancor
 * https://github.com/bancorprotocol/contracts
 * Modified from the original by Slava Balasanov
 * Split Power.sol out from BancorFormula.sol
 * Licensed to the Apache Software Foundation (ASF) under one or more contributor license agreements;
 * and to You under the Apache License, Version 2.0. "
 */
contract Power {
  string public version = "0.3";

  uint256 private constant ONE = 1;
  uint32 private constant MAX_WEIGHT = 1000000;
  uint8 private constant MIN_PRECISION = 32;
  uint8 private constant MAX_PRECISION = 127;

  /**
    The values below depend on MAX_PRECISION. If you choose to change it:
    Apply the same change in file 'PrintIntScalingFactors.py', run it and paste the results below.
  */
  uint256 private constant FIXED_1 = 0x080000000000000000000000000000000;
  uint256 private constant FIXED_2 = 0x100000000000000000000000000000000;
  uint256 private constant MAX_NUM = 0x1ffffffffffffffffffffffffffffffff;

  /**
    The values below depend on MAX_PRECISION. If you choose to change it:
    Apply the same change in file 'PrintLn2ScalingFactors.py', run it and paste the results below.
  */
  uint256 private constant LN2_MANTISSA = 0x2c5c85fdf473de6af278ece600fcbda;
  uint8   private constant LN2_EXPONENT = 122;

  /**
    The values below depend on MIN_PRECISION and MAX_PRECISION. If you choose to change either one of them:
    Apply the same change in file 'PrintFunctionBancorFormula.py', run it and paste the results below.
  */
  uint256[128] private maxExpArray;

  constructor()  public {
//  maxExpArray[  0] = 0x6bffffffffffffffffffffffffffffffff;
//  maxExpArray[  1] = 0x67ffffffffffffffffffffffffffffffff;
//  maxExpArray[  2] = 0x637fffffffffffffffffffffffffffffff;
//  maxExpArray[  3] = 0x5f6fffffffffffffffffffffffffffffff;
//  maxExpArray[  4] = 0x5b77ffffffffffffffffffffffffffffff;
//  maxExpArray[  5] = 0x57b3ffffffffffffffffffffffffffffff;
//  maxExpArray[  6] = 0x5419ffffffffffffffffffffffffffffff;
//  maxExpArray[  7] = 0x50a2ffffffffffffffffffffffffffffff;
//  maxExpArray[  8] = 0x4d517fffffffffffffffffffffffffffff;
//  maxExpArray[  9] = 0x4a233fffffffffffffffffffffffffffff;
//  maxExpArray[ 10] = 0x47165fffffffffffffffffffffffffffff;
//  maxExpArray[ 11] = 0x4429afffffffffffffffffffffffffffff;
//  maxExpArray[ 12] = 0x415bc7ffffffffffffffffffffffffffff;
//  maxExpArray[ 13] = 0x3eab73ffffffffffffffffffffffffffff;
//  maxExpArray[ 14] = 0x3c1771ffffffffffffffffffffffffffff;
//  maxExpArray[ 15] = 0x399e96ffffffffffffffffffffffffffff;
//  maxExpArray[ 16] = 0x373fc47fffffffffffffffffffffffffff;
//  maxExpArray[ 17] = 0x34f9e8ffffffffffffffffffffffffffff;
//  maxExpArray[ 18] = 0x32cbfd5fffffffffffffffffffffffffff;
//  maxExpArray[ 19] = 0x30b5057fffffffffffffffffffffffffff;
//  maxExpArray[ 20] = 0x2eb40f9fffffffffffffffffffffffffff;
//  maxExpArray[ 21] = 0x2cc8340fffffffffffffffffffffffffff;
//  maxExpArray[ 22] = 0x2af09481ffffffffffffffffffffffffff;
//  maxExpArray[ 23] = 0x292c5bddffffffffffffffffffffffffff;
//  maxExpArray[ 24] = 0x277abdcdffffffffffffffffffffffffff;
//  maxExpArray[ 25] = 0x25daf6657fffffffffffffffffffffffff;
//  maxExpArray[ 26] = 0x244c49c65fffffffffffffffffffffffff;
//  maxExpArray[ 27] = 0x22ce03cd5fffffffffffffffffffffffff;
//  maxExpArray[ 28] = 0x215f77c047ffffffffffffffffffffffff;
//  maxExpArray[ 29] = 0x1fffffffffffffffffffffffffffffffff;
//  maxExpArray[ 30] = 0x1eaefdbdabffffffffffffffffffffffff;
//  maxExpArray[ 31] = 0x1d6bd8b2ebffffffffffffffffffffffff;
    maxExpArray[ 32] = 0x1c35fedd14ffffffffffffffffffffffff;
    maxExpArray[ 33] = 0x1b0ce43b323fffffffffffffffffffffff;
    maxExpArray[ 34] = 0x19f0028ec1ffffffffffffffffffffffff;
    maxExpArray[ 35] = 0x18ded91f0e7fffffffffffffffffffffff;
    maxExpArray[ 36] = 0x17d8ec7f0417ffffffffffffffffffffff;
    maxExpArray[ 37] = 0x16ddc6556cdbffffffffffffffffffffff;
    maxExpArray[ 38] = 0x15ecf52776a1ffffffffffffffffffffff;
    maxExpArray[ 39] = 0x15060c256cb2ffffffffffffffffffffff;
    maxExpArray[ 40] = 0x1428a2f98d72ffffffffffffffffffffff;
    maxExpArray[ 41] = 0x13545598e5c23fffffffffffffffffffff;
    maxExpArray[ 42] = 0x1288c4161ce1dfffffffffffffffffffff;
    maxExpArray[ 43] = 0x11c592761c666fffffffffffffffffffff;
    maxExpArray[ 44] = 0x110a688680a757ffffffffffffffffffff;
    maxExpArray[ 45] = 0x1056f1b5bedf77ffffffffffffffffffff;
    maxExpArray[ 46] = 0x0faadceceeff8bffffffffffffffffffff;
    maxExpArray[ 47] = 0x0f05dc6b27edadffffffffffffffffffff;
    maxExpArray[ 48] = 0x0e67a5a25da4107fffffffffffffffffff;
    maxExpArray[ 49] = 0x0dcff115b14eedffffffffffffffffffff;
    maxExpArray[ 50] = 0x0d3e7a392431239fffffffffffffffffff;
    maxExpArray[ 51] = 0x0cb2ff529eb71e4fffffffffffffffffff;
    maxExpArray[ 52] = 0x0c2d415c3db974afffffffffffffffffff;
    maxExpArray[ 53] = 0x0bad03e7d883f69bffffffffffffffffff;
    maxExpArray[ 54] = 0x0b320d03b2c343d5ffffffffffffffffff;
    maxExpArray[ 55] = 0x0abc25204e02828dffffffffffffffffff;
    maxExpArray[ 56] = 0x0a4b16f74ee4bb207fffffffffffffffff;
    maxExpArray[ 57] = 0x09deaf736ac1f569ffffffffffffffffff;
    maxExpArray[ 58] = 0x0976bd9952c7aa957fffffffffffffffff;
    maxExpArray[ 59] = 0x09131271922eaa606fffffffffffffffff;
    maxExpArray[ 60] = 0x08b380f3558668c46fffffffffffffffff;
    maxExpArray[ 61] = 0x0857ddf0117efa215bffffffffffffffff;
    maxExpArray[ 62] = 0x07ffffffffffffffffffffffffffffffff;
    maxExpArray[ 63] = 0x07abbf6f6abb9d087fffffffffffffffff;
    maxExpArray[ 64] = 0x075af62cbac95f7dfa7fffffffffffffff;
    maxExpArray[ 65] = 0x070d7fb7452e187ac13fffffffffffffff;
    maxExpArray[ 66] = 0x06c3390ecc8af379295fffffffffffffff;
    maxExpArray[ 67] = 0x067c00a3b07ffc01fd6fffffffffffffff;
    maxExpArray[ 68] = 0x0637b647c39cbb9d3d27ffffffffffffff;
    maxExpArray[ 69] = 0x05f63b1fc104dbd39587ffffffffffffff;
    maxExpArray[ 70] = 0x05b771955b36e12f7235ffffffffffffff;
    maxExpArray[ 71] = 0x057b3d49dda84556d6f6ffffffffffffff;
    maxExpArray[ 72] = 0x054183095b2c8ececf30ffffffffffffff;
    maxExpArray[ 73] = 0x050a28be635ca2b888f77fffffffffffff;
    maxExpArray[ 74] = 0x04d5156639708c9db33c3fffffffffffff;
    maxExpArray[ 75] = 0x04a23105873875bd52dfdfffffffffffff;
    maxExpArray[ 76] = 0x0471649d87199aa990756fffffffffffff;
    maxExpArray[ 77] = 0x04429a21a029d4c1457cfbffffffffffff;
    maxExpArray[ 78] = 0x0415bc6d6fb7dd71af2cb3ffffffffffff;
    maxExpArray[ 79] = 0x03eab73b3bbfe282243ce1ffffffffffff;
    maxExpArray[ 80] = 0x03c1771ac9fb6b4c18e229ffffffffffff;
    maxExpArray[ 81] = 0x0399e96897690418f785257fffffffffff;
    maxExpArray[ 82] = 0x0373fc456c53bb779bf0ea9fffffffffff;
    maxExpArray[ 83] = 0x034f9e8e490c48e67e6ab8bfffffffffff;
    maxExpArray[ 84] = 0x032cbfd4a7adc790560b3337ffffffffff;
    maxExpArray[ 85] = 0x030b50570f6e5d2acca94613ffffffffff;
    maxExpArray[ 86] = 0x02eb40f9f620fda6b56c2861ffffffffff;
    maxExpArray[ 87] = 0x02cc8340ecb0d0f520a6af58ffffffffff;
    maxExpArray[ 88] = 0x02af09481380a0a35cf1ba02ffffffffff;
    maxExpArray[ 89] = 0x0292c5bdd3b92ec810287b1b3fffffffff;
    maxExpArray[ 90] = 0x0277abdcdab07d5a77ac6d6b9fffffffff;
    maxExpArray[ 91] = 0x025daf6654b1eaa55fd64df5efffffffff;
    maxExpArray[ 92] = 0x0244c49c648baa98192dce88b7ffffffff;
    maxExpArray[ 93] = 0x022ce03cd5619a311b2471268bffffffff;
    maxExpArray[ 94] = 0x0215f77c045fbe885654a44a0fffffffff;
    maxExpArray[ 95] = 0x01ffffffffffffffffffffffffffffffff;
    maxExpArray[ 96] = 0x01eaefdbdaaee7421fc4d3ede5ffffffff;
    maxExpArray[ 97] = 0x01d6bd8b2eb257df7e8ca57b09bfffffff;
    maxExpArray[ 98] = 0x01c35fedd14b861eb0443f7f133fffffff;
    maxExpArray[ 99] = 0x01b0ce43b322bcde4a56e8ada5afffffff;
    maxExpArray[100] = 0x019f0028ec1fff007f5a195a39dfffffff;
    maxExpArray[101] = 0x018ded91f0e72ee74f49b15ba527ffffff;
    maxExpArray[102] = 0x017d8ec7f04136f4e5615fd41a63ffffff;
    maxExpArray[103] = 0x016ddc6556cdb84bdc8d12d22e6fffffff;
    maxExpArray[104] = 0x015ecf52776a1155b5bd8395814f7fffff;
    maxExpArray[105] = 0x015060c256cb23b3b3cc3754cf40ffffff;
    maxExpArray[106] = 0x01428a2f98d728ae223ddab715be3fffff;
    maxExpArray[107] = 0x013545598e5c23276ccf0ede68034fffff;
    maxExpArray[108] = 0x01288c4161ce1d6f54b7f61081194fffff;
    maxExpArray[109] = 0x011c592761c666aa641d5a01a40f17ffff;
    maxExpArray[110] = 0x0110a688680a7530515f3e6e6cfdcdffff;
    maxExpArray[111] = 0x01056f1b5bedf75c6bcb2ce8aed428ffff;
    maxExpArray[112] = 0x00faadceceeff8a0890f3875f008277fff;
    maxExpArray[113] = 0x00f05dc6b27edad306388a600f6ba0bfff;
    maxExpArray[114] = 0x00e67a5a25da41063de1495d5b18cdbfff;
    maxExpArray[115] = 0x00dcff115b14eedde6fc3aa5353f2e4fff;
    maxExpArray[116] = 0x00d3e7a3924312399f9aae2e0f868f8fff;
    maxExpArray[117] = 0x00cb2ff529eb71e41582cccd5a1ee26fff;
    maxExpArray[118] = 0x00c2d415c3db974ab32a51840c0b67edff;
    maxExpArray[119] = 0x00bad03e7d883f69ad5b0a186184e06bff;
    maxExpArray[120] = 0x00b320d03b2c343d4829abd6075f0cc5ff;
    maxExpArray[121] = 0x00abc25204e02828d73c6e80bcdb1a95bf;
    maxExpArray[122] = 0x00a4b16f74ee4bb2040a1ec6c15fbbf2df;
    maxExpArray[123] = 0x009deaf736ac1f569deb1b5ae3f36c130f;
    maxExpArray[124] = 0x00976bd9952c7aa957f5937d790ef65037;
    maxExpArray[125] = 0x009131271922eaa6064b73a22d0bd4f2bf;
    maxExpArray[126] = 0x008b380f3558668c46c91c49a2f8e967b9;
    maxExpArray[127] = 0x00857ddf0117efa215952912839f6473e6;
  }

  /**
    General Description:
        Determine a value of precision.
        Calculate an integer approximation of (_baseN / _baseD) ^ (_expN / _expD) * 2 ^ precision.
        Return the result along with the precision used.

    Detailed Description:
        Instead of calculating "base ^ exp", we calculate "e ^ (ln(base) * exp)".
        The value of "ln(base)" is represented with an integer slightly smaller than "ln(base) * 2 ^ precision".
        The larger "precision" is, the more accurately this value represents the real value.
        However, the larger "precision" is, the more bits are required in order to store this value.
        And the exponentiation function, which takes "x" and calculates "e ^ x", is limited to a maximum exponent (maximum value of "x").
        This maximum exponent depends on the "precision" used, and it is given by "maxExpArray[precision] >> (MAX_PRECISION - precision)".
        Hence we need to determine the highest precision which can be used for the given input, before calling the exponentiation function.
        This allows us to compute "base ^ exp" with maximum accuracy and without exceeding 256 bits in any of the intermediate computations.
*/
  function power(uint256 _baseN, uint256 _baseD, uint32 _expN, uint32 _expD) internal view returns (uint256, uint8) {
    uint256 lnBaseTimesExp = ln(_baseN, _baseD) * _expN / _expD;
    uint8 precision = findPositionInMaxExpArray(lnBaseTimesExp);
    return (fixedExp(lnBaseTimesExp >> (MAX_PRECISION - precision), precision), precision);
  }

  /**
    Return floor(ln(numerator / denominator) * 2 ^ MAX_PRECISION), where:
    - The numerator   is a value between 1 and 2 ^ (256 - MAX_PRECISION) - 1
    - The denominator is a value between 1 and 2 ^ (256 - MAX_PRECISION) - 1
    - The output      is a value between 0 and floor(ln(2 ^ (256 - MAX_PRECISION) - 1) * 2 ^ MAX_PRECISION)
    This functions assumes that the numerator is larger than or equal to the denominator, because the output would be negative otherwise.
  */
  function ln(uint256 _numerator, uint256 _denominator) internal pure returns (uint256) {
    assert(_numerator <= MAX_NUM);

    uint256 res = 0;
    uint256 x = _numerator * FIXED_1 / _denominator;

    // If x >= 2, then we compute the integer part of log2(x), which is larger than 0.
    if (x >= FIXED_2) {
      uint8 count = floorLog2(x / FIXED_1);
      x >>= count; // now x < 2
      res = count * FIXED_1;
    }

    // If x > 1, then we compute the fraction part of log2(x), which is larger than 0.
    if (x > FIXED_1) {
      for (uint8 i = MAX_PRECISION; i > 0; --i) {
        x = (x * x) / FIXED_1; // now 1 < x < 4
        if (x >= FIXED_2) {
          x >>= 1; // now 1 < x < 2
          res += ONE << (i - 1);
        }
      }
    }

    return (res * LN2_MANTISSA) >> LN2_EXPONENT;
  }

  /**
    Compute the largest integer smaller than or equal to the binary logarithm of the input.
  */
  function floorLog2(uint256 _n) internal pure returns (uint8) {
    uint8 res = 0;
    uint256 n = _n;

    if (n < 256) {
      // At most 8 iterations
      while (n > 1) {
        n >>= 1;
        res += 1;
      }
    } else {
      // Exactly 8 iterations
      for (uint8 s = 128; s > 0; s >>= 1) {
        if (n >= (ONE << s)) {
          n >>= s;
          res |= s;
        }
      }
    }

    return res;
  }

  /**
      The global "maxExpArray" is sorted in descending order, and therefore the following statements are equivalent:
      - This function finds the position of [the smallest value in "maxExpArray" larger than or equal to "x"]
      - This function finds the highest position of [a value in "maxExpArray" larger than or equal to "x"]
  */
  function findPositionInMaxExpArray(uint256 _x) internal view returns (uint8) {
    uint8 lo = MIN_PRECISION;
    uint8 hi = MAX_PRECISION;

    while (lo + 1 < hi) {
      uint8 mid = (lo + hi) / 2;
      if (maxExpArray[mid] >= _x)
        lo = mid;
      else
        hi = mid;
    }

    if (maxExpArray[hi] >= _x)
        return hi;
    if (maxExpArray[lo] >= _x)
        return lo;

    assert(false);
    return 0;
  }

  /**
      This function can be auto-generated by the script 'PrintFunctionFixedExp.py'.
      It approximates "e ^ x" via maclaurin summation: "(x^0)/0! + (x^1)/1! + ... + (x^n)/n!".
      It returns "e ^ (x / 2 ^ precision) * 2 ^ precision", that is, the result is upshifted for accuracy.
      The global "maxExpArray" maps each "precision" to "((maximumExponent + 1) << (MAX_PRECISION - precision)) - 1".
      The maximum permitted value for "x" is therefore given by "maxExpArray[precision] >> (MAX_PRECISION - precision)".
  */
  function fixedExp(uint256 _x, uint8 _precision) internal pure returns (uint256) {
    uint256 xi = _x;
    uint256 res = 0;

    xi = (xi * _x) >> _precision;
    res += xi * 0x03442c4e6074a82f1797f72ac0000000; // add x^2 * (33! / 2!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x0116b96f757c380fb287fd0e40000000; // add x^3 * (33! / 3!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x0045ae5bdd5f0e03eca1ff4390000000; // add x^4 * (33! / 4!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x000defabf91302cd95b9ffda50000000; // add x^5 * (33! / 5!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x0002529ca9832b22439efff9b8000000; // add x^6 * (33! / 6!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x000054f1cf12bd04e516b6da88000000; // add x^7 * (33! / 7!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x00000a9e39e257a09ca2d6db51000000; // add x^8 * (33! / 8!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x0000012e066e7b839fa050c309000000; // add x^9 * (33! / 9!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x0000001e33d7d926c329a1ad1a800000; // add x^10 * (33! / 10!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x00000002bee513bdb4a6b19b5f800000; // add x^11 * (33! / 11!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x000000003a9316fa79b88eccf2a00000; // add x^12 * (33! / 12!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x00000000048177ebe1fa812375200000; // add x^13 * (33! / 13!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x00000000005263fe90242dcbacf00000; // add x^14 * (33! / 14!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x0000000000057e22099c030d94100000; // add x^15 * (33! / 15!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x00000000000057e22099c030d9410000; // add x^16 * (33! / 16!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x000000000000052b6b54569976310000; // add x^17 * (33! / 17!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x000000000000004985f67696bf748000; // add x^18 * (33! / 18!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x0000000000000003dea12ea99e498000; // add x^19 * (33! / 19!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x000000000000000031880f2214b6e000; // add x^20 * (33! / 20!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x0000000000000000025bcff56eb36000; // add x^21 * (33! / 21!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x0000000000000000001b722e10ab1000; // add x^22 * (33! / 22!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x00000000000000000001317c70077000; // add x^23 * (33! / 23!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x000000000000000000000cba84aafa00; // add x^24 * (33! / 24!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x000000000000000000000082573a0a00; // add x^25 * (33! / 25!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x000000000000000000000005035ad900; // add x^26 * (33! / 26!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x0000000000000000000000002f881b00; // add x^27 * (33! / 27!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x00000000000000000000000001b29340; // add x^28 * (33! / 28!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x000000000000000000000000000efc40; // add x^29 * (33! / 29!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x00000000000000000000000000007fe0; // add x^30 * (33! / 30!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x00000000000000000000000000000420; // add x^31 * (33! / 31!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x00000000000000000000000000000021; // add x^32 * (33! / 32!)
    xi = (xi * _x) >> _precision;
    res += xi * 0x00000000000000000000000000000001; // add x^33 * (33! / 33!)

    return res / 0x688589cc0e9505e2f2fee5580000000 + _x + (ONE << _precision); // divide by 33! and then add x^1 / 1! + x^0 / 0!
  }
}

/**
 * @title Bancor formula by Bancor
 * @dev Modified from the original by Slava Balasanov
 * https://github.com/bancorprotocol/contracts
 * Split Power.sol out from BancorFormula.sol and replace SafeMath formulas with zeppelin's SafeMath
 * Licensed to the Apache Software Foundation (ASF) under one or more contributor license agreements;
 * and to You under the Apache License, Version 2.0. "
 */
contract BancorFormula is Power {
  using SafeMath for uint256;

  string public version = "0.3";
  uint32 private constant MAX_WEIGHT = 1000000;

  /**
   * @dev given a token supply, connector balance, weight and a deposit amount (in the connector token),
   * calculates the return for a given conversion (in the main token)
   *
   * Formula:
   * Return = _supply * ((1 + _depositAmount / _connectorBalance) ^ (_connectorWeight / 1000000) - 1)
   *
   * @param _supply              token total supply
   * @param _connectorBalance    total connector balance
   * @param _connectorWeight     connector weight, represented in ppm, 1-1000000
   * @param _depositAmount       deposit amount, in connector token
   *
   *  @return purchase return amount
  */
  function calculatePurchaseReturn(
    uint256 _supply,
    uint256 _connectorBalance,
    uint32 _connectorWeight,
    uint256 _depositAmount) public view returns (uint256)
  {
    // validate input
    require(_supply > 0 && _connectorBalance > 0 && _connectorWeight > 0 && _connectorWeight <= MAX_WEIGHT);

    // special case for 0 deposit amount
    if (_depositAmount == 0) {
      return 0;
    }

    // special case if the weight = 100%
    if (_connectorWeight == MAX_WEIGHT) {
      return _supply.mul(_depositAmount).div(_connectorBalance);
    }

    uint256 result;
    uint8 precision;
    uint256 baseN = _depositAmount.add(_connectorBalance);
    (result, precision) = power(baseN, _connectorBalance, _connectorWeight, MAX_WEIGHT);
    uint256 temp = _supply.mul(result) >> precision;
    return temp - _supply;
  }

  /**
   * @dev given a token supply, connector balance, weight and a sell amount (in the main token),
   * calculates the return for a given conversion (in the connector token)
   *
   * Formula:
   * Return = _connectorBalance * (1 - (1 - _sellAmount / _supply) ^ (1 / (_connectorWeight / 1000000)))
   *
   * @param _supply              token total supply
   * @param _connectorBalance    total connector
   * @param _connectorWeight     constant connector Weight, represented in ppm, 1-1000000
   * @param _sellAmount          sell amount, in the token itself
   *
   * @return sale return amount
  */
  function calculateSaleReturn(uint256 _supply, uint256 _connectorBalance, uint32 _connectorWeight, uint256 _sellAmount) public view returns (uint256) {
    // validate input
    require(_supply > 0 && _connectorBalance > 0 && _connectorWeight > 0 && _connectorWeight <= MAX_WEIGHT && _sellAmount <= _supply);

    // special case for 0 sell amount
    if (_sellAmount == 0) {
      return 0;
    }

    // special case for selling the entire supply
    if (_sellAmount == _supply) {
      return _connectorBalance;
    }

    // special case if the weight = 100%
    if (_connectorWeight == MAX_WEIGHT) {
      return _connectorBalance.mul(_sellAmount).div(_supply);
    }

    uint256 result;
    uint8 precision;
    uint256 baseD = _supply - _sellAmount;
    (result, precision) = power(_supply, baseD, MAX_WEIGHT, _connectorWeight);
    uint256 oldBalance = _connectorBalance.mul(result);
    uint256 newBalance = _connectorBalance << precision;
    return oldBalance.sub(newBalance).div(result);
  }
}

/**
 * @title Bonding Curve
 * @dev Bonding curve contract based on Bacor formula
 * inspired by bancor protocol and simondlr
 * https://github.com/bancorprotocol/contracts
 * https://github.com/ConsenSys/curationmarkets/blob/master/CurationMarkets.sol
 */
contract BondingCurve is ERC20, BancorFormula, Ownable {

  /**
   * @dev Token configurations
   */
  string public name = "RADION";
  string public symbol = "RADIO";
  uint8 public decimals = 18;
  uint256 public constant MAX_SUPPLY = 3000000 * 10 ** 18;

  /**
   * @dev Whitelisted addresses are those that have registered on the website
   */
  mapping(address=>bool) whiteListedAddresses;

  /**
   * @dev Available balance of reserve token in contract
   */
  uint256 public poolBalance;

  /*
   * @dev reserve ratio, represented in ppm, 1-1000000
   * 1/3 corresponds to y= multiple * x^2
   * 1/2 corresponds to y= multiple * x
   * 2/3 corresponds to y= multiple * x^1/2
   * multiple will depends on contract initialization,
   * specificallytotalAmount and poolBalance parameters
   * we might want to add an 'initialize' function that will allow
   * the owner to send ether to the contract and mint a given amount of tokens
  */
  uint32 public reserveRatio = 1000000;

  /*
   * - Front-running attacks are currently mitigated by the following mechanisms:
   * TODO - minimum return argument for each conversion provides a way to define a minimum/maximum price for the transaction
   * - gas price limit prevents users from having control over the order of execution
  */
  uint256 public gasPrice = 0 wei; // maximum gas price for bancor transactions

  /**
   * @dev default function
   * gas ~ 91645
   */
  function() external payable {
    buy();
  }

  /**
   * @dev Buy tokens
   * gas ~ 77825
   * TODO implement maxAmount that helps prevent miner front-running
   */
  function buy() validGasPrice public payable returns(bool) {
    require(msg.value > 0);
    uint256 tokensToMint = calculatePurchaseReturn(_totalSupply, poolBalance, reserveRatio, msg.value);
    _totalSupply = _totalSupply.add(tokensToMint);
    require(_totalSupply <= MAX_SUPPLY);
    _balances[msg.sender] = _balances[msg.sender].add(tokensToMint);
    poolBalance = poolBalance.add(msg.value);
    emit LogMint(tokensToMint, msg.value);
    return true;
  }

  /**
   * @dev Sell tokens
   * gas ~ 86936
   * @param sellAmount Amount of tokens to withdraw
   * TODO implement maxAmount that helps prevent miner front-running
   */
  function sell(uint256 sellAmount) validGasPrice public returns(bool) {
    require(sellAmount > 0 && _balances[msg.sender] >= sellAmount);
    uint256 ethAmount = calculateSaleReturn(_totalSupply, poolBalance, reserveRatio, sellAmount);
    msg.sender.transfer(ethAmount);
    poolBalance = poolBalance.sub(ethAmount);
    _balances[msg.sender] = _balances[msg.sender].sub(sellAmount);
    _totalSupply = _totalSupply.sub(sellAmount);
    emit LogWithdraw(sellAmount, ethAmount);
    return true;
  }

  // verifies that the gas price is lower than the universal limit
  modifier validGasPrice() {
    assert(tx.gasprice <= gasPrice);
    _;
  }

  /**
   * @dev Allows the owner to update the gas price limit
   * @param _gasPrice The new gas price limit
  */
  function setGasPrice(uint256 _gasPrice) onlyOwner public {
    require(_gasPrice > 0);
    gasPrice = _gasPrice;
  }

  event LogMint(uint256 amountMinted, uint256 totalCost);
  event LogWithdraw(uint256 amountWithdrawn, uint256 reward);
  event LogBondingCurve(string logString, uint256 value);
}

contract BondingCurveMock is BondingCurve {
  constructor(
    uint256 _initialTotalSupply,
    uint32 _reserveRatio,
    uint256 _gasPrice) public payable
  {

    reserveRatio = _reserveRatio;
    _totalSupply = _initialTotalSupply;
    poolBalance = msg.value;
    gasPrice = _gasPrice;

    _balances[_owner] = _totalSupply;
    emit Transfer(address(0), _owner, _totalSupply);
  }
}