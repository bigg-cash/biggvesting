pragma solidity ^0.5.5;

/**
 * @dev Interface of the ERC20 standard as defined in the EIP. Does not include
 * the optional functions; to access them see {ERC20Detailed}.
 */
interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}


/**
 * @dev Wrappers over Solidity's arithmetic operations with added overflow
 * checks.
 *
 * Arithmetic operations in Solidity wrap on overflow. This can easily result
 * in bugs, because programmers usually assume that an overflow raises an
 * error, which is the standard behavior in high level programming languages.
 * `SafeMath` restores this intuition by reverting the transaction when an
 * operation overflows.
 *
 * Using this library instead of the unchecked operations eliminates an entire
 * class of bugs, so it's recommended to use it always.
 */
library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");

        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b <= a, "SafeMath: subtraction overflow");
        uint256 c = a - b;

        return c;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-solidity/pull/522
        if (a == 0) {
            return 0;
        }

        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");

        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        // Solidity only automatically asserts when dividing by 0
        require(b > 0, "SafeMath: division by zero");
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold

        return c;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b != 0, "SafeMath: modulo by zero");
        return a % b;
    }
}


/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * This test is non-exhaustive, and there may be false-negatives: during the
     * execution of a contract's constructor, its address will be reported as
     * not containing a contract.
     *
     * IMPORTANT: It is unsafe to assume that an address for which this
     * function returns false is an externally-owned account (EOA) and not a
     * contract.
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies in extcodesize, which returns 0 for contracts in
        // construction, since the code is only stored at the end of the
        // constructor execution.
        
        // According to EIP-1052, 0x0 is the value returned for not-yet created accounts
        // and 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 is returned
        // for accounts without code, i.e. `keccak256('')`
        bytes32 codehash;
        bytes32 accountHash = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470;
        // solhint-disable-next-line no-inline-assembly
        assembly { codehash := extcodehash(account) }
        return (codehash != 0x0 && codehash != accountHash);
    }

    /**
     * @dev Converts an `address` into `address payable`. Note that this is
     * simply a type cast: the actual underlying value is not changed.
     */
    function toPayable(address account) internal pure returns (address payable) {
        return address(uint160(account));
    }
}


/**
 * @title SafeERC20
 * @dev Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for ERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    using SafeMath for uint256;
    using Address for address;

    function safeTransfer(IERC20 token, address to, uint256 value) internal {
        callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(IERC20 token, address from, address to, uint256 value) internal {
        callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    function safeApprove(IERC20 token, address spender, uint256 value) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        // solhint-disable-next-line max-line-length
        require((value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).add(value);
        callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).sub(value);
        callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves.

        // A Solidity high level call has three parts:
        //  1. The target address is checked to verify it contains contract code
        //  2. The call itself is made, and success asserted
        //  3. The return value is decoded, which in turn checks the size of the returned data.
        // solhint-disable-next-line max-line-length
        require(address(token).isContract(), "SafeERC20: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = address(token).call(data);
        require(success, "SafeERC20: low-level call failed");

        if (returndata.length > 0) { // Return data is optional
            // solhint-disable-next-line max-line-length
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }
}


/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
contract Ownable {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor () internal {
        _owner = msg.sender;
        emit OwnershipTransferred(address(0), _owner);
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(isOwner(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Returns true if the caller is the current owner.
     */
    function isOwner() public view returns (bool) {
        return msg.sender == _owner;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public onlyOwner {
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     */
    function _transferOwnership(address newOwner) internal {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}


/**
 * @title TokenVesting
 * @dev A token holder contract that can release its token balance gradually like a
 * typical vesting scheme, with a cliff and vesting period. Optionally revocable by the
 * owner.
 */
contract BiggVesting is Ownable {
    // The vesting schedule is time-based (i.e. using block timestamps as opposed to e.g. block numbers), and is
    // therefore sensitive to timestamp manipulation (which is something miners can do, to a certain degree). Therefore,
    // it is recommended to avoid using short time durations (less than a minute). Typical vesting schemes, with a
    // cliff period of a year and a duration of four years, are safe to use.
    // solhint-disable not-rely-on-time

    using SafeMath for uint256;
    using SafeERC20 for IERC20;

    event BIGGVested(address _beneficiary, string _beneficiaryName, uint256 _startDate, uint256 _cliffPeriod, uint256 _vestDuration, uint256 _tokenVested, uint256 _vestType);
    event BIGGClaimed(address beneficiary, uint256 unClaimed);
    event BIGGRevoked(address beneficiary, uint256 refund);
    event BIGGWithdrawnUnvested(address owner, uint256 unvested);

    uint256 public totalTokensVested;
    uint256 public totalTokensClaimed;
    uint256 public totalTokensRevoked;

    address[] public vestedAddresses;
    uint256 public numberOfVesting;

    IERC20 private BIGG;
    uint8 private ACTIVE = 1;
    uint8 private FINISHED = 2;
    uint8 private REVOKED = 3;

    uint8 private STAFF = 1;
    uint8 private ANGELS = 2;
    uint8 private PRIVATE_SALE = 3;
    uint8 private PREPUBLIC_SALE = 4;

    uint256 public secondsInADay = 86400;

    struct Claim {
        uint256 date;
        uint256 amount;
        address claimedBy;
    }

    mapping (address => string) public beneficiaryNames;
    mapping (address => uint256) public startDates;
    mapping (address => uint256) public cliffPeriods;
    mapping (address => uint256) public vestDurations;
    mapping (address => uint256) public tokensVested;

    mapping (address => uint256) public vestingStatuses;
    mapping (address => uint256) public tokensClaimed;
    mapping (address => uint256) public lastClaimDates;
    mapping (address => uint256) public vestTypes;
    mapping (address => uint256) public tokensRevoked;
    mapping (address => uint256) public numberOfClaims;
    mapping (address => uint256) public revokeDates;

    mapping (address => Claim[]) public claims; 


    constructor(IERC20 _biggToken) public {
        require(address(_biggToken) != address(0x0));
        BIGG = _biggToken;
    }
    
    function addVesting(address _beneficiary, string memory _beneficiaryName, uint256 _startDate, uint256 _cliffPeriod, uint256 _vestDuration, uint256 _tokenVested, uint256 _vestType) public onlyOwner {

        uint256 epochToday = now.sub(now.mod(86400));
        require(_startDate >= epochToday);
        require(_beneficiary != address(0));
        require(_beneficiary != owner());
        require(startDates[_beneficiary] == 0);
        require(_cliffPeriod != 0);        
        require(_cliffPeriod <= _vestDuration);
        require(_tokenVested > 0);
        require(_vestType == STAFF || _vestType == ANGELS || _vestType == PRIVATE_SALE || _vestType == PREPUBLIC_SALE);
        uint256 totalTokenBalance = BIGG.balanceOf(address(this)).add(totalTokensClaimed).add(totalTokensRevoked);
        uint256 tokensToVest = _tokenVested.mul(10**18);
        require(totalTokensVested.add(tokensToVest) <= totalTokenBalance);

        beneficiaryNames[_beneficiary] = _beneficiaryName;
        startDates[_beneficiary] = _startDate;
        cliffPeriods[_beneficiary] = _cliffPeriod;
        vestDurations[_beneficiary] = _vestDuration;
        tokensVested[_beneficiary] = tokensToVest;
        vestTypes[_beneficiary] = _vestType;
        vestingStatuses[_beneficiary] = ACTIVE;

        totalTokensVested = totalTokensVested.add(tokensToVest);
        vestedAddresses.push(_beneficiary);
        numberOfVesting = numberOfVesting.add(1);
        
        emit BIGGVested(_beneficiary, _beneficiaryName, _startDate, _cliffPeriod, _vestDuration, _tokenVested, _vestType);
    }

    function claim(address _beneficiary) public {
        require(msg.sender == _beneficiary || msg.sender == owner());        
        uint256 unClaimed = availableToClaim(_beneficiary);
        require(unClaimed > 0);


        tokensClaimed[_beneficiary] = tokensClaimed[_beneficiary].add(unClaimed);
        BIGG.safeTransfer(_beneficiary, unClaimed);
        if (now >= startDates[_beneficiary] + vestDurations[_beneficiary].mul(secondsInADay))
            vestingStatuses[_beneficiary] = FINISHED;

        totalTokensClaimed = totalTokensClaimed.add(unClaimed);
        lastClaimDates[_beneficiary] = now;

        claims[_beneficiary].push(Claim(now, unClaimed, msg.sender));
        numberOfClaims[_beneficiary] = numberOfClaims[_beneficiary].add(1);
        emit BIGGClaimed(_beneficiary, unClaimed);
    }

    function revoke(address _beneficiary) public onlyOwner {
        require(vestingStatuses[_beneficiary] != REVOKED);

        uint256 balance = tokensVested[_beneficiary].sub(tokensClaimed[_beneficiary]);

        uint256 unClaimed = availableToClaim(_beneficiary);
        uint256 refund = balance.sub(unClaimed);
        vestingStatuses[_beneficiary] = REVOKED;
        if (refund != 0) {
            tokensRevoked[_beneficiary] = tokensRevoked[_beneficiary].add(refund);
            BIGG.safeTransfer(owner(), refund);
        }
        totalTokensRevoked = totalTokensRevoked.add(refund);        
        revokeDates[_beneficiary] = now;
        emit BIGGRevoked(_beneficiary, refund);
    }

    function withdrawUnvested() public onlyOwner {
 
        uint256 unvested = BIGG.balanceOf(address(this)).add(totalTokensClaimed).add(totalTokensRevoked).sub(totalTokensVested);

         if (unvested != 0) 
            BIGG.safeTransfer(owner(), unvested);
        
        emit BIGGWithdrawnUnvested(owner(), unvested);
    }

    function availableToClaim(address _beneficiary) public view returns (uint256) {
        if (vestTypes[_beneficiary] == PRIVATE_SALE || vestTypes[_beneficiary] == PREPUBLIC_SALE)
            return _vestAmtSale(_beneficiary).sub(tokensClaimed[_beneficiary]);
        else
            return _vestAmtStaff(_beneficiary).sub(tokensClaimed[_beneficiary]);        
    }

    function _vestAmtSale(address _beneficiary) private view returns (uint256) {
        uint256 totalBalance = tokensVested[_beneficiary].sub(tokensRevoked[_beneficiary]);
        uint256 cliffInSeconds = cliffPeriods[_beneficiary].mul(secondsInADay);

        if (now >= startDates[_beneficiary] + vestDurations[_beneficiary].mul(secondsInADay) || (vestingStatuses[_beneficiary] == REVOKED)) {
          return totalBalance;
        } else {
          uint256 secondsPassed;
          if (now < startDates[_beneficiary])
            secondsPassed = 0;
          else
            secondsPassed = now - startDates[_beneficiary];

          uint256 vestPortion = secondsPassed.div(cliffInSeconds); 
          return totalBalance.mul(vestPortion).mul(cliffPeriods[_beneficiary]).div(vestDurations[_beneficiary]);
        }
    }

    function _vestAmtStaff(address _beneficiary) private view returns (uint256) {
        uint256 totalBalance = tokensVested[_beneficiary].sub(tokensRevoked[_beneficiary]);
        uint256 cliffInSeconds = cliffPeriods[_beneficiary].mul(secondsInADay);

        if (now >= startDates[_beneficiary] + vestDurations[_beneficiary].mul(secondsInADay) || (vestingStatuses[_beneficiary] == REVOKED)) {
          return totalBalance;
        } else {           
          uint256 secondsPassed;
          if (now < startDates[_beneficiary])
            secondsPassed = 0;
          else
            secondsPassed = now - startDates[_beneficiary];
          uint256 vestPortion = secondsPassed.div(cliffInSeconds);
          if (secondsPassed != 0)
            vestPortion = vestPortion.add(1);           
          return totalBalance.mul(vestPortion).mul(cliffPeriods[_beneficiary]).div(vestDurations[_beneficiary].add(cliffPeriods[_beneficiary]));
        }
    }

    function getVestTotals() public view onlyOwner returns (uint256[6] memory vestTotals) {
        vestTotals[0] = BIGG.balanceOf(address(this)); 
        vestTotals[1] = numberOfVesting;
        vestTotals[2] = totalTokensVested;
        vestTotals[3] = totalTokensClaimed;
        vestTotals[4] = totalTokensRevoked;
        vestTotals[5] = BIGG.balanceOf(address(this)).add(totalTokensClaimed).add(totalTokensRevoked).sub(totalTokensVested);
    }

    function getBeneficiaries(uint256 start, uint256 howMany) public view onlyOwner returns (address[] memory) {

        if (start + howMany > numberOfVesting)
            howMany = start < numberOfVesting ? numberOfVesting - start : 0;

        address[] memory beneficiaries = new address[](howMany);

        uint256 j = 0;
        for (uint256 i=start; i < start+howMany; i++) {
            beneficiaries[j] = vestedAddresses[i];
            j++;
        }

        return beneficiaries;
    }

    function getVestInfo(address beneficiary) public view returns (string memory beneficiaryName, uint256[12] memory vestInfo) {
        beneficiaryName = beneficiaryNames[beneficiary];
        vestInfo[0] = startDates[beneficiary];
        vestInfo[1] = tokensVested[beneficiary];
        vestInfo[2] = cliffPeriods[beneficiary];
        vestInfo[3] = vestDurations[beneficiary];
        vestInfo[4] = tokensClaimed[beneficiary];
        vestInfo[5] = lastClaimDates[beneficiary];
        vestInfo[6] = numberOfClaims[beneficiary];
        vestInfo[7] = tokensRevoked[beneficiary];
        vestInfo[8] = revokeDates[beneficiary];
        vestInfo[9] = vestingStatuses[beneficiary];
        vestInfo[10] = vestTypes[beneficiary];
        vestInfo[11] = availableToClaim(beneficiary);
    }

    function transferOwnership(address newOwner) public onlyOwner {
        require(startDates[newOwner] == 0);
        super.transferOwnership(newOwner);
    }
}
